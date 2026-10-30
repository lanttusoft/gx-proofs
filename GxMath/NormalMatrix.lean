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
  gX — Normal Matrix Non-Degeneracy

  Salvaged from gameX lean/GameXProofs/NormalMatrix.lean, re-grounded:
  gX resources/shader/standard.vert:79 computes exactly
    mat3 normalMat = transpose(inverse(mat3(modelMat)));
  the mat3 extraction below models the GLSL mat3() of the
  transpose-uploaded row-major matrix (shader columns = engine rows,
  so mat3·v dots engine rows 0-2 with v — re-verified against the
  gX_Matrix layout in src/common/types/matrix.h).

  Salvage surgery: the gameX numeric instances (a 0.4-scale cube and a
  14×0.4×10 floor at captured scene positions) pin gameX scene data,
  not engine invariants — replaced by general diagonal-scale theorems.
  The structural mat3_ignores_column3 transfers unchanged.

  Key result: for any non-zero diagonal scale, the linear 3×3 part maps
  every non-zero normal to a non-zero vector — the normal-matrix path
  can never manufacture a zero normal out of a valid one.
-/

import GxMath.Matrix
import GxMath.Vector

open GxMath

namespace GxMath.NormalMatrix

/-!
## Helper: 3×3 linear part

Extract the upper-left 3×3 (engine rows 0-2) from a 4×4 matrix as a
function F32v3 → F32v3. This is what the shader's `mat3(modelMat)`
computes after the GL_TRUE-transposed upload.
-/
def mat3 (M : Matrix) : F32v3 → F32v3 := fun v =>
  { x := M.m0 * v.x + M.m4 * v.y + M.m8  * v.z
  , y := M.m1 * v.x + M.m5 * v.y + M.m9  * v.z
  , z := M.m2 * v.x + M.m6 * v.y + M.m10 * v.z
  }

/-!
## Theorem: mat3 only reads the linear part

For any matrix, mat3 reads m0-m10 which span engine rows 0-2.
Row 3 (m3, m7, m11, m15 = translation) is NOT read.
-/
theorem mat3_ignores_column3 (M : Matrix) :
  mat3 M = mat3 { M with m3 := 0, m7 := 0, m11 := 0, m15 := 1 } := by
  ext v <;> simp [mat3]

/-!
## Diagonal scale matrix (SRT model matrix with no rotation)

A model matrix with scale (sx, sy, sz), no rotation, and arbitrary
translation has the diagonal linear part diag(sx, sy, sz).
-/
def diagScale (sx sy sz tx ty tz : ℝ) : Matrix :=
  { m0 := sx, m1 := 0,  m2 := 0,  m3 := tx
  , m4 := 0,  m5 := sy, m6 := 0,  m7 := ty
  , m8 := 0,  m9 := 0,  m10 := sz, m11 := tz
  , m12 := 0, m13 := 0, m14 := 0,  m15 := 1
  }

/-!
## Lemma: mat3 of a diagonal scale ignores translation

mat3(diagScale …) = diag(sx, sy, sz) — the translation in row 3
(m3, m7, m11) is discarded.
-/
lemma diagScale_mat3_independent_of_translation (sx sy sz tx ty tz : ℝ) :
  mat3 (diagScale sx sy sz tx ty tz)
    = fun v => ({ x := sx * v.x, y := sy * v.y, z := sz * v.z } : F32v3) := by
  ext v <;> simp [diagScale, mat3]

/-!
## Theorem: diagonal-scale normal path preserves non-zero normals

mat3(diagScale) * n = (sx·nx, sy·ny, sz·nz) — never zero for any
non-zero n when all scales are non-zero.
-/
theorem diagScale_normal_nonzero (sx sy sz tx ty tz : ℝ)
    (hsx : sx ≠ 0) (hsy : sy ≠ 0) (hsz : sz ≠ 0)
    (n : F32v3) (hn : n.x ≠ 0 ∨ n.y ≠ 0 ∨ n.z ≠ 0) :
  (mat3 (diagScale sx sy sz tx ty tz)) n ≠ F32v3.zero := by
  intro h
  have hx := congrArg F32v3.x h
  have hy := congrArg F32v3.y h
  have hz := congrArg F32v3.z h
  simp [mat3, diagScale] at hx hy hz
  -- hx: sx * n.x = 0, hy: sy * n.y = 0, hz: sz * n.z = 0
  have hnx : n.x = 0 := (mul_eq_zero.mp hx).resolve_left hsx
  have hny : n.y = 0 := (mul_eq_zero.mp hy).resolve_left hsy
  have hnz : n.z = 0 := (mul_eq_zero.mp hz).resolve_left hsz
  rcases hn with (h | h | h)
  · exact h hnx
  · exact h hny
  · exact h hnz

/-!
## Corollary: uniform-scale normal path preserves non-zero normals

Uniform scale s ≠ 0: mat3 * n = s * n — never zero for non-zero n.
-/
theorem uniformScale_normal_nonzero (s tx ty tz : ℝ) (hs : s ≠ 0)
    (n : F32v3) (hn : n.x ≠ 0 ∨ n.y ≠ 0 ∨ n.z ≠ 0) :
  (mat3 (diagScale s s s tx ty tz)) n ≠ F32v3.zero := by
  exact diagScale_normal_nonzero s s s tx ty tz hs hs hs n hn

end GxMath.NormalMatrix
