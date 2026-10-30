/-
  SPDX-License-Identifier: GPL-3.0-or-later
  Copyright (c) 2025-2026 lanttu, opencode

  This file is part of gX proofs.
  gX proofs is free software: you can redistribute it and/or modify it under
  the terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
  gX proofs is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
  FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
  details.
  You should have received a copy of the GNU General Public License along with
  gX proofs. If not, see <https://www.gnu.org/licenses/>.
-/

/-
  //ai: exact-rational counterexample for box-exit projection when the emitter
  lies inside the probe volume. This pins only the owned fixture geometry and
  uses a rational witness ray, not a direction reconstructed from a captured
  pixel. It does not prove shader float behavior, raster visibility, or general
  scene intersection correctness.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace GxProofsGfx.ProbeBoxExit

structure Vec3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq

def pointOnRay (origin direction : Vec3) (t : ℚ) : Vec3 :=
  ⟨origin.x + t * direction.x,
   origin.y + t * direction.y,
   origin.z + t * direction.z⟩

def offset (a b : Vec3) : Vec3 :=
  ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

def probe : Vec3 := ⟨-3, 3 / 2, -3⟩
def receiver : Vec3 := ⟨6, 1 / 10, 1⟩
def witnessRay : Vec3 := ⟨1, 1, -1⟩

def emitterContains (p : Vec3) : Prop :=
  (34 / 5 : ℚ) ≤ p.x ∧ p.x ≤ 46 / 5 ∧
  (9 / 5 : ℚ) ≤ p.y ∧ p.y ≤ 21 / 5 ∧
  (-21 / 5 : ℚ) ≤ p.z ∧ p.z ≤ -9 / 5

def insideProbeBox (p : Vec3) : Prop :=
  (-50 : ℚ) ≤ p.x - probe.x ∧ p.x - probe.x ≤ 50 ∧
  (-12 : ℚ) ≤ p.y - probe.y ∧ p.y - probe.y ≤ 12 ∧
  (-50 : ℚ) ≤ p.z - probe.z ∧ p.z - probe.z ≤ 50

def localX : ℚ := receiver.x - probe.x
def localY : ℚ := receiver.y - probe.y
def localZ : ℚ := receiver.z - probe.z
def exitX : ℚ := (50 - localX) / witnessRay.x
def exitY : ℚ := (12 - localY) / witnessRay.y
def exitZ : ℚ := (-50 - localZ) / witnessRay.z

def emitterHit : Vec3 := pointOnRay receiver witnessRay 3
def boxExitPoint : Vec3 := pointOnRay receiver witnessRay exitY
def boxExitDirection : Vec3 := offset boxExitPoint probe

--ai: the existing component-scaled shader expression for this unit ray and box.
def componentProjectedDirection : Vec3 :=
  ⟨(localX + 50) / 50, (localY + 12) / 12, (localZ - 50) / 50⟩

theorem receiver_ray_hits_emitter : emitterContains emitterHit := by
  norm_num [emitterContains, emitterHit, pointOnRay, receiver, witnessRay]

theorem emitter_hit_is_inside_probe_box :
    insideProbeBox emitterHit ∧ (0 : ℚ) < 3 ∧ 3 < exitY := by
  norm_num [insideProbeBox, emitterHit, pointOnRay, receiver, witnessRay,
    probe, exitY, localY]

theorem positive_y_is_first_box_exit :
    0 < exitY ∧ exitY < exitX ∧ exitY < exitZ := by
  norm_num [exitX, exitY, exitZ, localX, localY, localZ,
    receiver, probe, witnessRay]

theorem box_exit_point_on_probe_boundary :
    insideProbeBox boxExitPoint ∧ boxExitPoint.y - probe.y = 12 := by
  norm_num [insideProbeBox, boxExitPoint, pointOnRay, exitY, localY,
    receiver, witnessRay, probe]

theorem probe_direction_to_actual_hit_reaches_emitter :
    emitterContains (pointOnRay probe (offset emitterHit probe) 1) := by
  norm_num [emitterContains, pointOnRay, offset, emitterHit,
    receiver, witnessRay, probe]

--ai: separated X-entry and Y-exit parameters cannot describe one intersecting ray.
theorem misses_emitter_of_x_entry_after_y_exit (direction : Vec3)
    (hx : (0 : ℚ) < direction.x) (hy : (0 : ℚ) < direction.y)
    (hseparated : (27 / 10 : ℚ) * direction.x < (49 / 5) * direction.y) :
    ∀ s : ℚ, 0 ≤ s → ¬ emitterContains (pointOnRay probe direction s) := by
  intro s hs hcontains
  rcases hcontains with ⟨hxlo, _, _, hyhi, _, _⟩
  dsimp [emitterContains, pointOnRay] at hxlo hyhi
  norm_num [probe] at hxlo hyhi
  have hxray : (49 / 5 : ℚ) ≤ s * direction.x := by linarith
  have hyray : s * direction.y ≤ (27 / 10 : ℚ) := by linarith
  have hxmul := mul_le_mul_of_nonneg_right hxray (le_of_lt hy)
  have hymul := mul_le_mul_of_nonneg_right hyray (le_of_lt hx)
  have hcross : (49 / 5 : ℚ) * direction.y ≤ (27 / 10) * direction.x := by
    calc
      (49 / 5 : ℚ) * direction.y ≤ (s * direction.x) * direction.y := hxmul
      _ = (s * direction.y) * direction.x := by ring
      _ ≤ (27 / 10 : ℚ) * direction.x := hymul
  linarith

theorem exact_box_exit_direction_misses_emitter :
    ∀ s : ℚ, 0 ≤ s → ¬ emitterContains (pointOnRay probe boxExitDirection s) := by
  apply misses_emitter_of_x_entry_after_y_exit boxExitDirection
  · norm_num [boxExitDirection, boxExitPoint, pointOnRay, offset,
      exitY, localY, receiver, witnessRay, probe]
  · norm_num [boxExitDirection, boxExitPoint, pointOnRay, offset,
      exitY, localY, receiver, witnessRay, probe]
  · norm_num [boxExitDirection, boxExitPoint, pointOnRay, offset,
      exitY, localY, receiver, witnessRay, probe]

theorem component_projected_direction_values :
    componentProjectedDirection = ⟨59 / 50, 53 / 60, -23 / 25⟩ := by
  norm_num [componentProjectedDirection, localX, localY, localZ,
    receiver, probe]

theorem component_projected_direction_misses_emitter :
    ∀ s : ℚ, 0 ≤ s →
      ¬ emitterContains (pointOnRay probe componentProjectedDirection s) := by
  apply misses_emitter_of_x_entry_after_y_exit componentProjectedDirection
  · norm_num [componentProjectedDirection, localX, receiver, probe]
  · norm_num [componentProjectedDirection, localY, receiver, probe]
  · norm_num [componentProjectedDirection, localX, localY, receiver, probe]

end GxProofsGfx.ProbeBoxExit
