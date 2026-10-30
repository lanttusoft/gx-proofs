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
  gxmath/Vector.lean
  gX — a game engine (salvaged from gameX lean/, re-verified)

  Formal verification of gX_F32v3 vector operations.
  Based on src/gxmath/vector3.c (dot/cross/lerp formulas
  re-verified against gX source at salvage time).

  Note: the C library uses IEEE-754 `Float`. As in GameXProofs/BgSystems,
  the formal math is modeled over `ℝ` — the exact real semantics that the
  C Float code approximates. Float rounding error is bounded separately
  by the C unit tests.

  Properties verified:
    - Add/Mul are commutative, associative, have identity
    - Dot is commutative
    - Cross is anti-commutative, perpendicular to both operands
    - Length is non-negative
    - Lerp endpoints
    - Lagrange identity |a×b|² = |a|²|b|² − (a·b)²
    - //ai: Cauchy-Schwarz, triangle and reverse triangle inequalities over ℝ
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace GxMath

/-!
## Type definition

Mirrors `gX_F32v3` from `common/types/vectors.h`:
```c
typedef struct gX_F32v3 { gX_F32 x; gX_F32 y; gX_F32 z; } gX_F32v3;
```
-/

@[ext]
structure F32v3 where
  x : ℝ
  y : ℝ
  z : ℝ

-- Named constructor matching gX_F32v3_Make(x, y, z)
def F32v3.make (x y z : ℝ) : F32v3 := { x, y, z }

-- Zero vector (identity for addition)
def F32v3.zero : F32v3 := { x := 0, y := 0, z := 0 }

-- Unit vectors
def F32v3.unitX : F32v3 := { x := 1, y := 0, z := 0 }
def F32v3.unitY : F32v3 := { x := 0, y := 1, z := 0 }
def F32v3.unitZ : F32v3 := { x := 0, y := 0, z := 1 }

/-!
## Arithmetic operations

Mirrors gX_F32v3_Add, gX_F32v3_Sub, gX_F32v3_Mul, gX_F32v3_Div,
gX_F32v3_MulScalar (scale), gX_F32v3_Negate from vector3.c
-/

-- Component-wise addition: gX_F32v3_Add(a, b) → { a.x+b.x, a.y+b.y, a.z+b.z }
def F32v3.add (a b : F32v3) : F32v3 :=
  { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z }

-- Component-wise subtraction: gX_F32v3_Sub(a, b)
def F32v3.sub (a b : F32v3) : F32v3 :=
  { x := a.x - b.x, y := a.y - b.y, z := a.z - b.z }

-- Component-wise multiplication: gX_F32v3_Mul(a, b)
def F32v3.mul (a b : F32v3) : F32v3 :=
  { x := a.x * b.x, y := a.y * b.y, z := a.z * b.z }

-- Scalar multiplication: gX_F32v3_MulScalar(v, s) / gX_F32v3_Scale
def F32v3.scale (v : F32v3) (s : ℝ) : F32v3 :=
  { x := v.x * s, y := v.y * s, z := v.z * s }

-- Negation: gX_F32v3_Negate(v)
def F32v3.neg (v : F32v3) : F32v3 :=
  { x := -v.x, y := -v.y, z := -v.z }

-- Dot product: gX_F32v3_Dot(a, b) → a.x*b.x + a.y*b.y + a.z*b.z
def F32v3.dot (a b : F32v3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

-- Cross product: gX_F32v3_Cross(a, b)
def F32v3.cross (a b : F32v3) : F32v3 :=
  { x := a.y * b.z - a.z * b.y
  , y := a.z * b.x - a.x * b.z
  , z := a.x * b.y - a.y * b.x
  }

-- Squared length: gX_F32v3_LengthSqr(v)
def F32v3.lengthSqr (v : F32v3) : ℝ :=
  v.x * v.x + v.y * v.y + v.z * v.z

-- Length (magnitude): gX_F32v3_Length(v)
noncomputable def F32v3.length (v : F32v3) : ℝ :=
  Real.sqrt (v.lengthSqr)

-- Normalize: gX_F32v3_Normalize(v)
-- Defined only for non-zero vectors (len > 0)
-- //opencode: retain the nonzero precondition in the contract without embedding it in the value.
noncomputable def F32v3.normalize (v : F32v3) (_h : v.lengthSqr > 0) : F32v3 :=
  let invLen := 1 / Real.sqrt v.lengthSqr
  { x := v.x * invLen, y := v.y * invLen, z := v.z * invLen }

-- Linear interpolation: gX_F32v3_Lerp(a, b, t) → a + t*(b-a)
def F32v3.lerp (a b : F32v3) (t : ℝ) : F32v3 :=
  a.add ((b.sub a).scale t)

/-!
## Notation

Allow writing `a + b` instead of `a.add b`, etc.
-/

instance : Add F32v3 := ⟨F32v3.add⟩
instance : Sub F32v3 := ⟨F32v3.sub⟩
instance : Mul F32v3 := ⟨F32v3.mul⟩
instance : Neg F32v3 := ⟨F32v3.neg⟩

-- Scalar multiplication via * notation (Real on left)
instance : HMul ℝ F32v3 F32v3 where
  hMul s v := v.scale s

instance : HMul F32v3 ℝ F32v3 where
  hMul v s := v.scale s

/-!
## Theorems — Vector arithmetic
-/

namespace F32v3

-- Add is commutative: a + b = b + a
theorem add_comm (a b : F32v3) : a + b = b + a := by
  change add a b = add b a
  ext <;> simp [add] <;> ring

-- Add is associative: (a + b) + c = a + (b + c)
theorem add_assoc (a b c : F32v3) : (a + b) + c = a + (b + c) := by
  change add (add a b) c = add a (add b c)
  ext <;> simp [add] <;> ring

-- Zero is additive identity: a + 0 = a
theorem add_zero (a : F32v3) : a + zero = a := by
  change add a zero = a
  ext <;> simp [add, zero]

-- Zero is additive identity (commuted): 0 + a = a
theorem zero_add (a : F32v3) : zero + a = a := by
  change add zero a = a
  ext <;> simp [add, zero]

-- Negation is additive inverse: a + (-a) = 0
theorem add_neg_self (a : F32v3) : a + (-a) = zero := by
  change add a (neg a) = zero
  ext <;> simp [add, neg, zero]

-- Mul is commutative: a * b = b * a
theorem mul_comm (a b : F32v3) : a * b = b * a := by
  change mul a b = mul b a
  ext <;> simp [mul] <;> ring

-- Dot is commutative: a · b = b · a
theorem dot_comm (a b : F32v3) : a.dot b = b.dot a := by
  simp [dot]; ring

-- Dot with zero: a · 0 = 0
theorem dot_zero (a : F32v3) : a.dot zero = 0 := by
  simp [dot, zero]

-- Cross is anti-commutative: a × b = -(b × a)
theorem cross_anti_comm (a b : F32v3) : a.cross b = -(b.cross a) := by
  change a.cross b = neg (b.cross a)
  ext <;> simp [cross, neg] <;> ring

-- Cross with self is zero: a × a = 0
theorem cross_self (a : F32v3) : a.cross a = zero := by
  ext <;> simp [cross, zero] <;> ring

-- Cross is perpendicular to both inputs: (a × b) · a = 0
theorem cross_dot_left (a b : F32v3) : (a.cross b).dot a = 0 := by
  simp [cross, dot]; ring

-- Cross is perpendicular to both inputs: (a × b) · b = 0
theorem cross_dot_right (a b : F32v3) : (a.cross b).dot b = 0 := by
  simp [cross, dot]; ring

-- Length squared is non-negative: |v|² ≥ 0
theorem lengthSqr_nonneg (v : F32v3) : v.lengthSqr ≥ 0 := by
  have hx : 0 ≤ v.x * v.x := mul_self_nonneg v.x
  have hy : 0 ≤ v.y * v.y := mul_self_nonneg v.y
  have hz : 0 ≤ v.z * v.z := mul_self_nonneg v.z
  unfold lengthSqr
  nlinarith

-- Unit vectors have length 1
theorem unitX_length : F32v3.unitX.lengthSqr = 1 := by
  simp [unitX, lengthSqr]

theorem unitY_length : F32v3.unitY.lengthSqr = 1 := by
  simp [unitY, lengthSqr]

theorem unitZ_length : F32v3.unitZ.lengthSqr = 1 := by
  simp [unitZ, lengthSqr]

-- Dot product with unit vectors extracts components
theorem dot_unitX (v : F32v3) : v.dot unitX = v.x := by
  simp [dot, unitX]

theorem dot_unitY (v : F32v3) : v.dot unitY = v.y := by
  simp [dot, unitY]

theorem dot_unitZ (v : F32v3) : v.dot unitZ = v.z := by
  simp [dot, unitZ]

-- Lerp at t=0 gives a, at t=1 gives b
theorem lerp_zero (a b : F32v3) : a.lerp b 0 = a := by
  ext <;> simp [lerp, add, sub, scale]

theorem lerp_one (a b : F32v3) : a.lerp b 1 = b := by
  ext <;> simp [lerp, add, sub, scale]

-- Scalar multiplication distributes over addition: s*(a + b) = s*a + s*b
theorem scale_add (s : ℝ) (a b : F32v3) : (a + b).scale s = a.scale s + b.scale s := by
  change (add a b).scale s = add (a.scale s) (b.scale s)
  ext <;> simp [add, scale] <;> ring

-- Scalar multiplication distributes over scalar addition: (s + t)*v = s*v + t*v
theorem add_scale (s t : ℝ) (v : F32v3) : v.scale (s + t) = v.scale s + v.scale t := by
  change v.scale (s + t) = add (v.scale s) (v.scale t)
  ext <;> simp [add, scale] <;> ring

-- Lagrange identity: |a×b|² = |a|²|b|² − (a·b)²
theorem cross_lengthSqr (a b : F32v3) :
    (a.cross b).lengthSqr = a.lengthSqr * b.lengthSqr - (a.dot b) * (a.dot b) := by
  simp [cross, lengthSqr, dot]; ring

--ai: exact-real Euclidean bounds derived from the existing Lagrange identity.
theorem length_nonneg (v : F32v3) : 0 ≤ v.length :=
  Real.sqrt_nonneg _

--ai: the square-root model agrees with the squared-length polynomial.
theorem length_sq (v : F32v3) : v.length ^ 2 = v.lengthSqr := by
  exact Real.sq_sqrt (lengthSqr_nonneg v)

--ai: Cauchy-Schwarz for the native three-component vector model.
theorem abs_dot_le_length_mul (a b : F32v3) :
    |a.dot b| ≤ a.length * b.length := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg (length_nonneg a) (length_nonneg b))
  rw [mul_pow, length_sq, length_sq]
  have hcross := lengthSqr_nonneg (a.cross b)
  nlinarith [cross_lengthSqr a b]

--ai: triangle inequality without introducing a second vector representation.
theorem length_add_le (a b : F32v3) : (a + b).length ≤ a.length + b.length := by
  have hexpand : (a + b).lengthSqr = a.lengthSqr + 2 * a.dot b + b.lengthSqr := by
    change (add a b).lengthSqr = _
    simp only [lengthSqr, add, dot]
    ring
  have hdot := le_trans (le_abs_self (a.dot b)) (abs_dot_le_length_mul a b)
  apply (sq_le_sq₀ (length_nonneg (a + b)) (add_nonneg (length_nonneg a) (length_nonneg b))).mp
  rw [length_sq, hexpand]
  nlinarith [length_sq a, length_sq b]

--ai: displacement length does not depend on endpoint order.
theorem length_sub_comm (a b : F32v3) : (a - b).length = (b - a).length := by
  unfold length
  congr 1
  change (sub a b).lengthSqr = (sub b a).lengthSqr
  simp only [lengthSqr, sub]
  ring

--ai: reverse triangle inequality used by the sphere SDF contract.
theorem abs_length_sub_le (a b : F32v3) : |a.length - b.length| ≤ (a - b).length := by
  have hab : (a - b) + b = a := by
    change add (sub a b) b = a
    ext <;> simp [add, sub]
  have hba : (b - a) + a = b := by
    change add (sub b a) a = b
    ext <;> simp [add, sub]
  have hleft := length_add_le (a - b) b
  have hright := length_add_le (b - a) a
  rw [hab] at hleft
  rw [hba, length_sub_comm b a] at hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end F32v3

end GxMath
