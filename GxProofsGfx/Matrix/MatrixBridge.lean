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
  gX — matrix model bridge

  The proof corpus uses several matrix representations because they answer
  different questions:

  * GxMath.Matrix: logical row-major 4×4 over ℝ.
  * MatrixField.Matrix: flat numeric-field order over ℝ.
  * GxMath.ClipMatrix.Mat4: row-vector clip model over ℚ.
  * GfxTemporalMatrix / CofactorInverse: camera-history and ideal-inverse
    contracts built on the clip model.

  This module records the algebraic conversions. It does not claim that the
  physical C struct, a GLSL upload, or a GL readback is byte-identical.
-/

import GxMath.Matrix
import GxProofsGfx.Matrix.MatrixField
import GxMath.ClipMatrix

namespace GxProofsGfx.Matrix.MatrixBridge
open GxMath.ClipMatrix

open GxProofsGfx

def ofFlat (M : MatrixField.Matrix) : GxMath.Matrix :=
  { m0 := M.m0, m1 := M.m1, m2 := M.m2, m3 := M.m3
    m4 := M.m4, m5 := M.m5, m6 := M.m6, m7 := M.m7
    m8 := M.m8, m9 := M.m9, m10 := M.m10, m11 := M.m11
    m12 := M.m12, m13 := M.m13, m14 := M.m14, m15 := M.m15 }

def ofClip (M : Mat4) : GxMath.Matrix :=
  { m0 := (M.m00 : ℝ), m1 := (M.m01 : ℝ), m2 := (M.m02 : ℝ), m3 := (M.m03 : ℝ)
    m4 := (M.m10 : ℝ), m5 := (M.m11 : ℝ), m6 := (M.m12 : ℝ), m7 := (M.m13 : ℝ)
    m8 := (M.m20 : ℝ), m9 := (M.m21 : ℝ), m10 := (M.m22 : ℝ), m11 := (M.m23 : ℝ)
    m12 := (M.m30 : ℝ), m13 := (M.m31 : ℝ), m14 := (M.m32 : ℝ), m15 := (M.m33 : ℝ) }

theorem ofFlat_transpose (M : MatrixField.Matrix) :
    ofFlat (MatrixField.transpose M) = GxMath.Matrix.transpose (ofFlat M) := by
  ext <;> simp [ofFlat, MatrixField.transpose, GxMath.Matrix.transpose]

theorem ofFlat_multiply (A B : MatrixField.Matrix) :
    ofFlat (MatrixField.multiply A B)
      = GxMath.Matrix.mul (ofFlat A) (ofFlat B) := by
  ext <;> simp [ofFlat, MatrixField.multiply, GxMath.Matrix.mul]

theorem ofClip_transpose (M : Mat4) :
    ofClip (transpose M) = GxMath.Matrix.transpose (ofClip M) := by
  ext <;> simp [ofClip, transpose, GxMath.Matrix.transpose]

theorem ofClip_matId :
    ofClip matId = GxMath.Matrix.identity := by
  ext <;> norm_num [ofClip, matId, GxMath.Matrix.identity]

theorem ofClip_matMul (A B : Mat4) :
    ofClip (matMul A B)
      = GxMath.Matrix.mul (ofClip A) (ofClip B) := by
  ext <;> simp [ofClip, matMul, GxMath.Matrix.mul]

end GxProofsGfx.Matrix.MatrixBridge
