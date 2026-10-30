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
  gX — Matrix Convention Proof (field-level)

  Field-level counterpart to GfxMatrix (which proves the same
  convention via Mathlib matrices): struct layout m0..m15 and the
  multiply formula re-verified against src/gxmath/matrix.c
  (result.m0 = l.m0*r.m0 + l.m1*r.m4 + … matches exactly).

  Salvage surgery: columnMajor_upload dropped — it models the
  gX_Matrix_SetRowMajor(0) compat mode, which does not exist in gX.
  Everything kept is pure math over the verified layout.

  Theorems proven: 6
    - transpose_involution, transpose_get, rm_to_cm_involution,
      multiply_get, transpose_mul, transpose_mul_equiv
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.MatrixField

-- 4×4 matrix with row-major storage (m0..m3 = row 0, etc.)
@[ext]
structure Matrix where
  m0  : ℝ
  m1  : ℝ
  m2  : ℝ
  m3  : ℝ
  m4  : ℝ
  m5  : ℝ
  m6  : ℝ
  m7  : ℝ
  m8  : ℝ
  m9  : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m13 : ℝ
  m14 : ℝ
  m15 : ℝ

-- Transpose: swap rows and columns (m[i*4+j] ↔ m[j*4+i])
def transpose (M : Matrix) : Matrix :=
  { m0 := M.m0, m1 := M.m4, m2 := M.m8,  m3 := M.m12
  , m4 := M.m1, m5 := M.m5, m6 := M.m9,  m7 := M.m13
  , m8 := M.m2, m9 := M.m6, m10 := M.m10, m11 := M.m14
  , m12 := M.m3, m13 := M.m7, m14 := M.m11, m15 := M.m15
  }

theorem transpose_involution (M : Matrix) : transpose (transpose M) = M := by
  ext <;> simp [transpose]

-- Element access by (row, column) indices (0-3, with bounds)
def get (M : Matrix) (r c : Nat) : ℝ :=
  match r, c with
  | 0, 0 => M.m0  | 0, 1 => M.m1  | 0, 2 => M.m2  | 0, 3 => M.m3
  | 1, 0 => M.m4  | 1, 1 => M.m5  | 1, 2 => M.m6  | 1, 3 => M.m7
  | 2, 0 => M.m8  | 2, 1 => M.m9  | 2, 2 => M.m10 | 2, 3 => M.m11
  | 3, 0 => M.m12 | 3, 1 => M.m13 | 3, 2 => M.m14 | 3, 3 => M.m15
  | _, _ => 0

theorem transpose_get (M : Matrix) (r c : Nat) (hr : r < 4) (hc : c < 4) :
    get (transpose M) r c = get M c r := by
  have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases hr4 with (rfl|rfl|rfl|rfl)
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [transpose, get]
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [transpose, get]
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [transpose, get]
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [transpose, get]

--ai: numeric-field storage permutation; actual raw C upload also depends on physical layout.
def rowMajorToColMajor (R : Matrix) : Matrix := transpose R

theorem rm_to_cm_involution (R : Matrix) :
    rowMajorToColMajor (rowMajorToColMajor R) = R := by
  unfold rowMajorToColMajor; simp [transpose]

-- Row-major matrix multiplication: (A × B)[i][j] = sum_k A[i][k] * B[k][j]
def multiply (A B : Matrix) : Matrix :=
  { m0  := A.m0*B.m0  + A.m1*B.m4  + A.m2*B.m8   + A.m3*B.m12
  , m1  := A.m0*B.m1  + A.m1*B.m5  + A.m2*B.m9   + A.m3*B.m13
  , m2  := A.m0*B.m2  + A.m1*B.m6  + A.m2*B.m10  + A.m3*B.m14
  , m3  := A.m0*B.m3  + A.m1*B.m7  + A.m2*B.m11  + A.m3*B.m15
  , m4  := A.m4*B.m0  + A.m5*B.m4  + A.m6*B.m8   + A.m7*B.m12
  , m5  := A.m4*B.m1  + A.m5*B.m5  + A.m6*B.m9   + A.m7*B.m13
  , m6  := A.m4*B.m2  + A.m5*B.m6  + A.m6*B.m10  + A.m7*B.m14
  , m7  := A.m4*B.m3  + A.m5*B.m7  + A.m6*B.m11  + A.m7*B.m15
  , m8  := A.m8*B.m0  + A.m9*B.m4  + A.m10*B.m8  + A.m11*B.m12
  , m9  := A.m8*B.m1  + A.m9*B.m5  + A.m10*B.m9  + A.m11*B.m13
  , m10 := A.m8*B.m2  + A.m9*B.m6  + A.m10*B.m10 + A.m11*B.m14
  , m11 := A.m8*B.m3  + A.m9*B.m7  + A.m10*B.m11 + A.m11*B.m15
  , m12 := A.m12*B.m0 + A.m13*B.m4 + A.m14*B.m8  + A.m15*B.m12
  , m13 := A.m12*B.m1 + A.m13*B.m5 + A.m14*B.m9  + A.m15*B.m13
  , m14 := A.m12*B.m2 + A.m13*B.m6 + A.m14*B.m10 + A.m15*B.m14
  , m15 := A.m12*B.m3 + A.m13*B.m7 + A.m14*B.m11 + A.m15*B.m15
  }

theorem multiply_get (A B : Matrix) (r c : Nat) (hr : r < 4) (hc : c < 4) :
    get (multiply A B) r c = (get A r 0 * get B 0 c + get A r 1 * get B 1 c +
                              get A r 2 * get B 2 c + get A r 3 * get B 3 c) := by
  have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases hr4 with (rfl|rfl|rfl|rfl)
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [multiply, get]
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [multiply, get]
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [multiply, get]
  · rcases hc4 with (rfl|rfl|rfl|rfl) <;> simp [multiply, get]

-- (A × B)^T = B^T × A^T — the identity the old Float model couldn't prove.
theorem transpose_mul (A B : Matrix) : transpose (multiply A B) = multiply (transpose B) (transpose A) := by
  ext <;> simp [transpose, multiply] <;> ring

-- Element-wise equivalent statement of transpose_mul.
-- //opencode: equality is extensional for all indices, so bounds are unused.
theorem transpose_mul_equiv (A B : Matrix) (i j : Nat) (_hi : i < 4) (_hj : j < 4) :
    get (transpose (multiply A B)) i j = get (multiply (transpose B) (transpose A)) i j := by
  rw [transpose_mul]

end GxProofsGfx.MatrixField
