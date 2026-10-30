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
  gX — Point-shadow caster containment Specification (Mathlib tier)

  Models the guard in src/renderer/gfx/draw.c
  gX_RendererGFX_PointShadow_Draw: a caster whose local-space AABB
  contains the light is skipped, because such a caster blocks every
  direction of the point light's cube and blackens the whole scene
  (the lamp bulb around its own point light is the common case — it
  made every shadow-casting light contribute exactly nothing until
  the guard landed).

  The engine transforms the light into the model's local space with
  the inverse TRS (gX_Matrix_Invert + gX_F32v3_Transform) and tests
  the model's local AABB. The spec proves that test is exactly
  world-space containment in the transformed box: the guard is sound
  (a light inside the transformed box is skipped) and complete (a
  skipped light is inside it), for any invertible affine transform.
  The matrix-level inverse/transpose conventions are pinned by
  GfxMatrix/GfxMatrixConv; this file pins the containment algebra.

  Theorems proven: 6
    - inv_apply_apply:     inverse then forward is the identity
    - apply_inv_apply:     forward then inverse is the identity
    - guard_iff_world:     the local test ↔ world containment
    - guard_skip_of_world: a light inside the transformed box is skipped
    - guard_light_of_not:  a light outside it is never skipped
    - guard_identity:      the identity transform is the plain AABB test
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Pi

namespace GxProofsGfx.ShadowContain

abbrev Vec := Fin 3 → ℝ

structure Box where
  lo : Vec
  hi : Vec

def Box.Contains (b : Box) (x : Vec) : Prop :=
  (∀ i, b.lo i ≤ x i) ∧ (∀ i, x i ≤ b.hi i)

-- The engine's TRS: an invertible linear part plus a translation.
structure Affine where
  lin : Vec ≃ₗ[ℝ] Vec
  t : Vec

def Affine.apply (T : Affine) (x : Vec) : Vec := T.lin x + T.t

def Affine.invApply (T : Affine) (y : Vec) : Vec := T.lin.symm (y - T.t)

-- The guard's decision: skip iff the light's local image is in the box.
def GuardSkip (T : Affine) (b : Box) (light : Vec) : Prop :=
  b.Contains (T.invApply light)

-- 1/2. The inverse round trips.
theorem inv_apply_apply (T : Affine) (x : Vec) :
    T.invApply (T.apply x) = x := by
  simp [Affine.invApply, Affine.apply]

theorem apply_inv_apply (T : Affine) (y : Vec) :
    T.apply (T.invApply y) = y := by
  simp [Affine.invApply, Affine.apply]

-- 3. The local-space test is exactly world containment in T's image of
-- the box (soundness and completeness of the guard).
theorem guard_iff_world (T : Affine) (b : Box) (light : Vec) :
    GuardSkip T b light ↔ ∃ x, b.Contains x ∧ T.apply x = light := by
  constructor
  · intro h
    exact ⟨T.invApply light, h, apply_inv_apply T light⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [GuardSkip, inv_apply_apply] using hx

-- 4. Soundness: a light inside the transformed box is skipped.
theorem guard_skip_of_world (T : Affine) (b : Box) (x : Vec)
    (hx : b.Contains x) : GuardSkip T b (T.apply x) := by
  simpa [GuardSkip, inv_apply_apply] using hx

-- 5. Completeness: a light outside the transformed box is never skipped.
theorem guard_light_of_not (T : Affine) (b : Box) (light : Vec)
    (h : ¬ ∃ x, b.Contains x ∧ T.apply x = light) : ¬ GuardSkip T b light := by
  intro hg
  exact h ((guard_iff_world T b light).mp hg)

-- 6. The identity transform degenerates to the plain local AABB test.
theorem guard_identity (b : Box) (light : Vec) :
    GuardSkip ⟨LinearEquiv.refl ℝ Vec, 0⟩ b light ↔ b.Contains light := by
  simp [GuardSkip, Affine.invApply]

end GxProofsGfx.ShadowContain
