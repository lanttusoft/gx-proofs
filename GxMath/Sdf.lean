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
  gxmath/Sdf.lean
  gX — a game engine

  Formal contracts for the signed-distance primitives in
  src/gxmath/sdf.c.

  The model is over ℝ and uses F32v3.length/F32v3.dot. It does not certify
  IEEE sqrt, GPU evaluation, or Lipschitz behavior of the approximate cone.
  The plane model assumes a unit normal; the C helper normalizes its input.
  //ai: exact unit length is a hypothesis, not a certified float normalization
  bound. Clearance theorems do not certify the native/GPU raymarcher.

  Theorems proven:
    - sphere zero/sign correspondence with the radius
    - plane linearity and zero at the origin
    - torus center distance
    - cube corner distance
    - capsule with a zero-length segment
    - sphere and unit-normal plane are 1-Lipschitz in exact real arithmetic
    - nonnegative/positive clearance inside their exact-real step bounds
    - any 1-Lipschitz field preserves its sign under a step no longer than |field|
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import GxMath.Vector

namespace GxMath
namespace Sdf

open F32v3

noncomputable def sphere (p : F32v3) (radius : ℝ) : ℝ :=
  p.length - radius

def plane (p normal : F32v3) : ℝ :=
  p.dot normal

noncomputable def cube (p bounds : F32v3) : ℝ :=
  let qx := |p.x| - bounds.x
  let qy := |p.y| - bounds.y
  let qz := |p.z| - bounds.z
  let inside := min (max qx (max qy qz)) 0
  Real.sqrt (max qx 0 ^ 2 + max qy 0 ^ 2 + max qz 0 ^ 2) + inside

noncomputable def torus (p : F32v3) (major minor : ℝ) : ℝ :=
  let radial := Real.sqrt (p.x ^ 2 + p.z ^ 2)
  Real.sqrt ((radial - major) ^ 2 + p.y ^ 2) - minor

noncomputable def capsule (p a b : F32v3) (radius : ℝ) : ℝ :=
  let axis := b - a
  let denom := axis.lengthSqr
  let h := if denom > 0 then max 0 (min 1 (((p - a).dot axis) / denom)) else 0
  (p - (a + axis.scale h)).length - radius

theorem sphere_eq_zero_iff (p : F32v3) (radius : ℝ) :
    sphere p radius = 0 ↔ p.length = radius := by
  unfold sphere
  constructor <;> intro h
  · linarith
  · linarith

theorem sphere_nonpos_iff (p : F32v3) (radius : ℝ) :
    sphere p radius ≤ 0 ↔ p.length ≤ radius := by
  unfold sphere
  constructor <;> intro h
  · linarith
  · linarith

theorem plane_zero (normal : F32v3) : plane zero normal = 0 := by
  simp [plane, dot, zero]

theorem plane_add (p q normal : F32v3) :
    plane (p + q) normal = plane p normal + plane q normal := by
  unfold plane dot
  change (p.x + q.x) * normal.x + (p.y + q.y) * normal.y + (p.z + q.z) * normal.z =
    (p.x * normal.x + p.y * normal.y + p.z * normal.z) +
      (q.x * normal.x + q.y * normal.y + q.z * normal.z)
  ring

theorem plane_smul (s : ℝ) (p normal : F32v3) :
    plane (p.scale s) normal = s * plane p normal := by
  unfold plane dot
  change (p.x * s) * normal.x + (p.y * s) * normal.y + (p.z * s) * normal.z =
    s * (p.x * normal.x + p.y * normal.y + p.z * normal.z)
  ring

theorem torus_center (major minor : ℝ) (hmajor : 0 < major) :
    torus zero major minor = major - minor := by
  simp [torus, zero, Real.sqrt_sq_eq_abs, abs_of_pos hmajor]

theorem cube_corner (bounds : F32v3)
    (hx : 0 < bounds.x) (hy : 0 < bounds.y) (hz : 0 < bounds.z) :
    cube bounds bounds = 0 := by
  simp [cube, abs_of_pos hx, abs_of_pos hy, abs_of_pos hz]

theorem capsule_zero_segment (p a : F32v3) (radius : ℝ) :
    capsule p a a radius = (p - a).length - radius := by
  have hzero : a - a = F32v3.zero := by
    change F32v3.sub a a = F32v3.zero
    ext <;> simp [F32v3.sub, F32v3.zero]
  have hadd : a + F32v3.zero = a := by
    change F32v3.add a F32v3.zero = a
    ext <;> simp [F32v3.add, F32v3.zero]
  have hscale : F32v3.zero.scale 0 = F32v3.zero := by
    ext <;> simp [F32v3.scale, F32v3.zero]
  simp [capsule, hzero, F32v3.lengthSqr, F32v3.zero]
  change (p - (a + F32v3.zero.scale 0)).length = (p - a).length
  rw [hscale, hadd]

--ai: radius subtraction cancels, leaving the reverse triangle inequality.
theorem sphere_lipschitz (p q : F32v3) (radius : ℝ) :
    |sphere p radius - sphere q radius| ≤ (p - q).length := by
  have hcancel : sphere p radius - sphere q radius = p.length - q.length := by
    unfold sphere
    ring
  rw [hcancel]
  exact abs_length_sub_le p q

--ai: a one-Lipschitz field cannot cross zero when a step is bounded by |field|.
theorem lipschitz_step_preserves_sign (f : F32v3 → ℝ) (p q : F32v3)
    (hlipschitz : ∀ x y, |f x - f y| ≤ (x - y).length)
    (hstep : (p - q).length ≤ |f p|) :
    (0 ≤ f p → 0 ≤ f q) ∧ (f p ≤ 0 → f q ≤ 0) := by
  constructor
  · intro hp
    have hdiff := abs_le.mp (hlipschitz p q)
    have hbound : (p - q).length ≤ f p := by
      simpa [abs_of_nonneg hp] using hstep
    have hupper : f p - f q ≤ (p - q).length := hdiff.2
    linarith
  · intro hp
    have hdiff := abs_le.mp (hlipschitz p q)
    have hbound : (p - q).length ≤ -f p := by
      simpa [abs_of_nonpos hp] using hstep
    have hlower : -(p - q).length ≤ f p - f q := hdiff.1
    linarith

--ai: the unnormalized plane has Lipschitz constant equal to its normal length.
theorem plane_lipschitz_bound (p q normal : F32v3) :
    |plane p normal - plane q normal| ≤ (p - q).length * normal.length := by
  have hdelta : plane p normal - plane q normal = (p - q).dot normal := by
    unfold plane dot
    change _ = (p.x - q.x) * normal.x + (p.y - q.y) * normal.y +
      (p.z - q.z) * normal.z
    ring
  rw [hdelta]
  exact abs_dot_le_length_mul (p - q) normal

--ai: unit length is an explicit hypothesis, not assumed C normalization accuracy.
theorem plane_lipschitz (p q normal : F32v3) (hunit : normal.length = 1) :
    |plane p normal - plane q normal| ≤ (p - q).length := by
  simpa [hunit] using plane_lipschitz_bound p q normal

--ai: these clearance results do not certify a floating-point raymarcher.
theorem sphere_step_nonneg (p q : F32v3) (radius : ℝ)
    (hstep : (p - q).length ≤ sphere p radius) : 0 ≤ sphere q radius := by
  have hdiff := (abs_le.mp (sphere_lipschitz p q radius)).2
  linarith

--ai: strictly shorter displacement stays on the positive side of the sphere.
theorem sphere_step_pos (p q : F32v3) (radius : ℝ)
    (hstep : (p - q).length < sphere p radius) : 0 < sphere q radius := by
  have hdiff := (abs_le.mp (sphere_lipschitz p q radius)).2
  linarith

--ai: a unit-normal plane also bounds nonnegative clearance after displacement.
theorem plane_step_nonneg (p q normal : F32v3) (hunit : normal.length = 1)
    (hstep : (p - q).length ≤ plane p normal) : 0 ≤ plane q normal := by
  have hdiff := (abs_le.mp (plane_lipschitz p q normal hunit)).2
  linarith

--ai: strictly shorter displacement stays on the plane's positive side.
theorem plane_step_pos (p q normal : F32v3) (hunit : normal.length = 1)
    (hstep : (p - q).length < plane p normal) : 0 < plane q normal := by
  have hdiff := (abs_le.mp (plane_lipschitz p q normal hunit)).2
  linarith

end Sdf
end GxMath
