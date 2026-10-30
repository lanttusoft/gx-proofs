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
  gX — Matrix upload-convention specification (Mathlib tier)

  //ai: Abstract flat-tuple interpretation identities, not a complete upload proof.
  Numeric fields m0..m3 form row 0 of logical R, but gX_Matrix's physical
  struct begins m0,m4,m8,m12. Passing &matrix.m0 is NOT passing the tuple
  m0,m1,...,m15. GfxTemporalMatrix models this permutation and GL_TRUE
  separately; the runtime convention must not be flipped.

  Transpose involution does not prove an actual GL readback or distinguish
  transpose flags. The product-transpose identity does not certify a foreign
  C multiply implementation. Singular matrices can legitimately yield w=0.

  Theorems proven: 3
    - upload_transpose:      transpose ∘ row-major = column-major
    - transpose_involutive:  abstract double transpose
    - foreign_mul_transpose: (B×A)^T = A^T×B^T (algebra only)
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul

namespace GxProofsGfx.MatrixTuple

open Matrix

-- Flat index: row i, col j of a 4×4 in a 16-tuple.
def idx (i j : Fin 4) : Fin 16 :=
  ⟨i.val * 4 + j.val, by
    have hi := i.is_lt
    have hj := j.is_lt
    omega⟩

-- gxmath reading: m0..m3 = row 0 (row-major).
def ofRowMajor (v : Fin 16 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => v (idx i j)

-- GLSL reading: first four = column 0 (column-major).
def ofColMajor (v : Fin 16 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => v (idx j i)

--ai: abstract tuple interpretations; physical struct upload is modeled separately.
theorem upload_transpose (v : Fin 16 → ℝ) :
    (ofRowMajor v)ᵀ = ofColMajor v := by
  ext i j
  rfl

--ai: transposing twice is the identity, not evidence from glGetUniformfv.
theorem transpose_involutive (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (Mᵀ)ᵀ = M :=
  Matrix.transpose_transpose M

--ai: product-transpose identity only; raylib implementation correspondence is not proved.
theorem foreign_mul_transpose (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    (B * A)ᵀ = Aᵀ * Bᵀ :=
  Matrix.transpose_mul B A
