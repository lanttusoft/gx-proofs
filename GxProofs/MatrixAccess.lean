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
  gX — Matrix Access Convention

  Proves the correct row-major access pattern for gX_Matrix.

  Salvaged from gameX lean/GameXProofs/MatrixAccess.lean, re-verified:
  src/common/types/matrix.h declares row 0 as m0,m4,m8,m12
  (flat indices 0,1,2,3), row 1 as m1,m5,m9,m13, etc. — so flat
  index row*4+col is row-major element access, matching the gameX
  spec's Matrix4 layout exactly. Proofs (simp/rfl over Float)
  transfer unchanged.

  Row-major matrix-vector multiplication: result[i] = sum_j M[i][j] * v[j]
  In flat array: result[i] = sum_j m[i*4 + j] * v[j]

  Column access (WRONG):  result[i] = sum_j m[j*4 + i] * v[j]  = M^T × v
  Row access (CORRECT):   result[i] = sum_j m[i*4 + j] * v[j]  = M  × v
-/

namespace GxProofs.MatrixAccess

-- The 16 flat indices for a row-major 4×4 matrix
-- Row i starts at index i*4, column j is at offset j
structure Matrix4 where
  m0  : Float
  m1  : Float
  m2  : Float
  m3  : Float
  m4  : Float
  m5  : Float
  m6  : Float
  m7  : Float
  m8  : Float
  m9  : Float
  m10 : Float
  m11 : Float
  m12 : Float
  m13 : Float
  m14 : Float
  m15 : Float

-- Flat array view of the struct
def flat (M : Matrix4) (i : Nat) : Float :=
  match i with
  | 0 => M.m0 | 1 => M.m1 | 2 => M.m2 | 3 => M.m3
  | 4 => M.m4 | 5 => M.m5 | 6 => M.m6 | 7 => M.m7
  | 8 => M.m8 | 9 => M.m9 | 10 => M.m10 | 11 => M.m11
  | 12 => M.m12 | 13 => M.m13 | 14 => M.m14 | 15 => M.m15
  | _ => 0

-- Row-major element access: element at (row, col) is at flat index row*4 + col
def elemAt (M : Matrix4) (row col : Nat) : Float :=
  flat M (row * 4 + col)

-- Row-major M × v: result[i] = sum_j M[i][j] * v[j]
def mulRowMajor (M : Matrix4) (x y z w : Float) : (Float × Float × Float × Float) :=
  ( elemAt M 0 0 * x + elemAt M 0 1 * y + elemAt M 0 2 * z + elemAt M 0 3 * w
  , elemAt M 1 0 * x + elemAt M 1 1 * y + elemAt M 1 2 * z + elemAt M 1 3 * w
  , elemAt M 2 0 * x + elemAt M 2 1 * y + elemAt M 2 2 * z + elemAt M 2 3 * w
  , elemAt M 3 0 * x + elemAt M 3 1 * y + elemAt M 3 2 * z + elemAt M 3 3 * w
  )

-- Column access (WRONG): computes M^T × v instead of M × v
def mulColumn (M : Matrix4) (x y z w : Float) : (Float × Float × Float × Float) :=
  ( flat M 0 * x + flat M 4 * y + flat M 8  * z + flat M 12 * w  -- col 0
  , flat M 1 * x + flat M 5 * y + flat M 9  * z + flat M 13 * w  -- col 1
  , flat M 2 * x + flat M 6 * y + flat M 10 * z + flat M 14 * w  -- col 2
  , flat M 3 * x + flat M 7 * y + flat M 11 * z + flat M 15 * w  -- col 3
  )

-- The relationship between row-major and column access:
-- column access on M = row-major access on M^T (transpose)
def transpose (M : Matrix4) : Matrix4 :=
  { m0 := M.m0, m1 := M.m4, m2 := M.m8,  m3 := M.m12
  , m4 := M.m1, m5 := M.m5, m6 := M.m9,  m7 := M.m13
  , m8 := M.m2, m9 := M.m6, m10 := M.m10, m11 := M.m14
  , m12 := M.m3, m13 := M.m7, m14 := M.m11, m15 := M.m15
  }

-- Column access on M equals row-major access on M^T
theorem columnAccess_equals_transpose_mul (M : Matrix4) (x y z w : Float) :
    mulColumn M x y z w = mulRowMajor (transpose M) x y z w := by
  simp [mulColumn, mulRowMajor, transpose, flat, elemAt]

-- Row-major M × v with flat array indices:
--   result[0] = m[0]*x + m[1]*y + m[2]*z + m[3]*w   (row 0)
--   result[1] = m[4]*x + m[5]*y + m[6]*z + m[7]*w   (row 1)
--   result[2] = m[8]*x + m[9]*y + m[10]*z + m[11]*w  (row 2)
--   result[3] = m[12]*x + m[13]*y + m[14]*z + m[15]*w (row 3)
theorem row_major_flat_formula (M : Matrix4) (x y z w : Float) :
    mulRowMajor M x y z w =
    ( flat M 0 * x + flat M 1 * y + flat M 2  * z + flat M 3  * w
    , flat M 4 * x + flat M 5 * y + flat M 6  * z + flat M 7  * w
    , flat M 8 * x + flat M 9 * y + flat M 10 * z + flat M 11 * w
    , flat M 12 * x + flat M 13 * y + flat M 14 * z + flat M 15 * w
    ) := by
  simp [mulRowMajor, flat, elemAt]

-- Column access with flat array indices (the WRONG pattern):
--   result[0] = m[0]*x + m[4]*y + m[8]*z + m[12]*w  (column 0)
--   result[1] = m[1]*x + m[5]*y + m[9]*z + m[13]*w  (column 1)
--   result[2] = m[2]*x + m[6]*y + m[10]*z + m[14]*w (column 2)
--   result[3] = m[3]*x + m[7]*y + m[11]*z + m[15]*w (column 3)
-- This is equivalent to M^T × v, which gives the INVERSE rotation for
-- a rotation matrix (since R^T = R^{-1} for orthonormal matrices).
theorem column_flat_formula (M : Matrix4) (x y z w : Float) :
    mulColumn M x y z w =
    ( flat M 0 * x + flat M 4 * y + flat M 8  * z + flat M 12 * w
    , flat M 1 * x + flat M 5 * y + flat M 9  * z + flat M 13 * w
    , flat M 2 * x + flat M 6 * y + flat M 10 * z + flat M 14 * w
    , flat M 3 * x + flat M 7 * y + flat M 11 * z + flat M 15 * w
    ) := rfl

end GxProofs.MatrixAccess
