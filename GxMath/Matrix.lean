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
  gxmath/Matrix.lean
  gX — a game engine (salvaged from gameX lean/, re-verified)

  Formal verification of gX_Matrix (4×4) operations.
  Based on src/gxmath/matrix.c (row-major m0..m3 = row 0,
  standard A×B multiply — re-verified against gX source).

  Row-major storage: m0..m3 = row 0, m4..m7 = row 1, etc.
  Mirrors gX_Matrix struct: { m0..m15: Float }

  Note: the C library uses IEEE-754 `Float`. The formal math is modeled
  over `ℝ` — the exact real semantics the Float code approximates.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import GxMath.Vector

namespace GxMath

open F32v3

/-!
## Type definition

Mirrors `gX_Matrix` from `common/types/matrix.h`:
```c
typedef struct gX_Matrix {
    gX_F32 m0, m4,  m8, m12;
    gX_F32 m1, m5,  m9, m13;
    gX_F32 m2, m6, m10, m14;
    gX_F32 m3, m7, m11, m15;
} gX_Matrix;
```
-/

@[ext]
structure Matrix where
  m0 : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ
  m4 : ℝ
  m5 : ℝ
  m6 : ℝ
  m7 : ℝ
  m8 : ℝ
  m9 : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m13 : ℝ
  m14 : ℝ
  m15 : ℝ

namespace Matrix

-- Identity matrix: gX_Matrix_Identity()
def identity : Matrix :=
  { m0 := 1, m1 := 0, m2 := 0, m3 := 0
  , m4 := 0, m5 := 1, m6 := 0, m7 := 0
  , m8 := 0, m9 := 0, m10:= 1, m11:= 0
  , m12:= 0, m13:= 0, m14:= 0, m15:= 1
  }

-- Zero matrix
def zero : Matrix :=
  { m0 := 0, m1 := 0, m2 := 0, m3 := 0
  , m4 := 0, m5 := 0, m6 := 0, m7 := 0
  , m8 := 0, m9 := 0, m10:= 0, m11:= 0
  , m12:= 0, m13:= 0, m14:= 0, m15:= 0
  }

/-!
## Matrix multiplication: gX_Matrix_Multiply(a, b) = a × b

Standard 4×4 matrix product: (a×b)[i][j] = Σₖ a[i][k] * b[k][j]
In numeric-field row-major: result.m(4i+j) = Σₖ a.m(4i+k) * b.m(4k+j).
//ai: the physical C struct interleaves m0,m4,m8,m12; it is not numeric-field order.
-/
def mul (a b : Matrix) : Matrix :=
  { m0  := a.m0*b.m0  + a.m1*b.m4  + a.m2*b.m8   + a.m3*b.m12
  , m1  := a.m0*b.m1  + a.m1*b.m5  + a.m2*b.m9   + a.m3*b.m13
  , m2  := a.m0*b.m2  + a.m1*b.m6  + a.m2*b.m10  + a.m3*b.m14
  , m3  := a.m0*b.m3  + a.m1*b.m7  + a.m2*b.m11  + a.m3*b.m15
  , m4  := a.m4*b.m0  + a.m5*b.m4  + a.m6*b.m8   + a.m7*b.m12
  , m5  := a.m4*b.m1  + a.m5*b.m5  + a.m6*b.m9   + a.m7*b.m13
  , m6  := a.m4*b.m2  + a.m5*b.m6  + a.m6*b.m10  + a.m7*b.m14
  , m7  := a.m4*b.m3  + a.m5*b.m7  + a.m6*b.m11  + a.m7*b.m15
  , m8  := a.m8*b.m0  + a.m9*b.m4  + a.m10*b.m8  + a.m11*b.m12
  , m9  := a.m8*b.m1  + a.m9*b.m5  + a.m10*b.m9  + a.m11*b.m13
  , m10 := a.m8*b.m2  + a.m9*b.m6  + a.m10*b.m10 + a.m11*b.m14
  , m11 := a.m8*b.m3  + a.m9*b.m7  + a.m10*b.m11 + a.m11*b.m15
  , m12 := a.m12*b.m0 + a.m13*b.m4 + a.m14*b.m8  + a.m15*b.m12
  , m13 := a.m12*b.m1 + a.m13*b.m5 + a.m14*b.m9  + a.m15*b.m13
  , m14 := a.m12*b.m2 + a.m13*b.m6 + a.m14*b.m10 + a.m15*b.m14
  , m15 := a.m12*b.m3 + a.m13*b.m7 + a.m14*b.m11 + a.m15*b.m15
  }

-- Matrix addition (component-wise)
def add (a b : Matrix) : Matrix :=
  { m0  := a.m0  + b.m0,  m1  := a.m1  + b.m1,  m2  := a.m2  + b.m2,  m3  := a.m3  + b.m3
  , m4  := a.m4  + b.m4,  m5  := a.m5  + b.m5,  m6  := a.m6  + b.m6,  m7  := a.m7  + b.m7
  , m8  := a.m8  + b.m8,  m9  := a.m9  + b.m9,  m10 := a.m10 + b.m10, m11 := a.m11 + b.m11
  , m12 := a.m12 + b.m12, m13 := a.m13 + b.m13, m14 := a.m14 + b.m14, m15 := a.m15 + b.m15
  }

-- Scalar multiplication
def scale (m : Matrix) (s : ℝ) : Matrix :=
  { m0  := m.m0  * s, m1  := m.m1  * s, m2  := m.m2  * s, m3  := m.m3  * s
  , m4  := m.m4  * s, m5  := m.m5  * s, m6  := m.m6  * s, m7  := m.m7  * s
  , m8  := m.m8  * s, m9  := m.m9  * s, m10 := m.m10 * s, m11 := m.m11 * s
  , m12 := m.m12 * s, m13 := m.m13 * s, m14 := m.m14 * s, m15 := m.m15 * s
  }

-- Transpose: gX_Matrix_Transpose(m)
def transpose (m : Matrix) : Matrix :=
  { m0  := m.m0, m1  := m.m4, m2  := m.m8,  m3  := m.m12
  , m4  := m.m1, m5  := m.m5, m6  := m.m9,  m7  := m.m13
  , m8  := m.m2, m9  := m.m6, m10 := m.m10, m11 := m.m14
  , m12 := m.m3, m13 := m.m7, m14 := m.m11, m15 := m.m15
  }

-- Vector transformation: gX_F32v3_Transform(v, mat)
-- Treats vector as (x, y, z, 1) column, multiplies mat * v
def transformVec (m : Matrix) (v : F32v3) : F32v3 :=
  { x := m.m0 * v.x + m.m4 * v.y + m.m8  * v.z + m.m12
  , y := m.m1 * v.x + m.m5 * v.y + m.m9  * v.z + m.m13
  , z := m.m2 * v.x + m.m6 * v.y + m.m10 * v.z + m.m14
  }

-- Trace: sum of diagonal elements
def trace (m : Matrix) : ℝ :=
  m.m0 + m.m5 + m.m10 + m.m15

instance : Mul Matrix := ⟨mul⟩
instance : Add Matrix := ⟨add⟩
instance : HMul ℝ Matrix Matrix where
  hMul s m := m.scale s

instance : HMul Matrix ℝ Matrix where
  hMul m s := m.scale s

/-!
## Theorems
-/

-- Identity is multiplicative identity: I * A = A
theorem mul_identity_left (a : Matrix) : identity * a = a := by
  change mul identity a = a
  ext <;> simp [identity, mul]

-- Identity is multiplicative identity (right): A * I = A
theorem mul_identity_right (a : Matrix) : a * identity = a := by
  change mul a identity = a
  ext <;> simp [identity, mul]

-- Zero matrix annihilates: 0 * A = 0
theorem mul_zero_left (a : Matrix) : zero * a = zero := by
  change mul zero a = zero
  ext <;> simp [zero, mul]

-- Zero matrix annihilates (right): A * 0 = 0
theorem mul_zero_right (a : Matrix) : a * zero = zero := by
  change mul a zero = zero
  ext <;> simp [zero, mul]

-- Add is commutative: A + B = B + A
theorem add_comm (a b : Matrix) : a + b = b + a := by
  change add a b = add b a
  ext <;> simp [add] <;> ring

-- Add is associative: (A + B) + C = A + (B + C)
theorem add_assoc (a b c : Matrix) : (a + b) + c = a + (b + c) := by
  change add (add a b) c = add a (add b c)
  ext <;> simp [add] <;> ring

-- Transpose of transpose is identity: (Aᵀ)ᵀ = A
theorem transpose_transpose (m : Matrix) : m.transpose.transpose = m := by
  ext <;> simp [transpose]

-- Transpose of product: (A * B)ᵀ = Bᵀ * Aᵀ
theorem transpose_mul (a b : Matrix) : (a * b).transpose = b.transpose * a.transpose := by
  change (mul a b).transpose = mul b.transpose a.transpose
  ext <;> simp [mul, transpose] <;> ring

-- Transform of zero vector: M * 0 = w-axis (0,0,0)
theorem transformVec_zero (m : Matrix) : m.transformVec F32v3.zero = { x := m.m12, y := m.m13, z := m.m14 } := by
  simp [transformVec, F32v3.zero]

-- Identity transforms vector unchanged (for w=1 case)
theorem transformVec_identity (v : F32v3) : identity.transformVec v = v := by
  ext <;> simp [transformVec, identity]

-- Transform distributes over vector addition for DIRECTION vectors (w=0):
-- the translation column is dropped, so M·(a+b) = M·a + M·b.
-- (The full affine transform with w=1 is NOT linear in this sense —
--  the translation term m12 would appear twice.)
def transformDir (m : Matrix) (v : F32v3) : F32v3 :=
  { x := m.m0 * v.x + m.m4 * v.y + m.m8  * v.z
  , y := m.m1 * v.x + m.m5 * v.y + m.m9  * v.z
  , z := m.m2 * v.x + m.m6 * v.y + m.m10 * v.z
  }

theorem transformDir_add (m : Matrix) (a b : F32v3) :
    m.transformDir (a + b) = m.transformDir a + m.transformDir b := by
  change m.transformDir (F32v3.add a b) = F32v3.add (m.transformDir a) (m.transformDir b)
  ext <;> simp [transformDir, F32v3.add] <;> ring

-- Trace is linear: tr(s*A) = s * tr(A)
theorem trace_scale (s : ℝ) (m : Matrix) : (m.scale s).trace = s * m.trace := by
  simp [trace, scale]; ring

-- Transpose preserves trace: tr(A) = tr(Aᵀ)
theorem trace_transpose (m : Matrix) : m.transpose.trace = m.trace := by
  simp [trace, transpose]

--ai: distinguishes C's multiplication order from the former opposite-product model.
theorem asymmetric_composition_witness :
    (mul { identity with m12 := 2 } { identity with m0 := 3 }).m12 = 6 ∧
    (mul { identity with m0 := 3 } { identity with m12 := 2 }).m12 = 2 := by
  norm_num [mul, identity]

end Matrix
end GxMath
