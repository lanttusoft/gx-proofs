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
  //ai: exact-rational mirror of src/gxmath/matrix.c:83-119.
  Numeric fields m0..m15 correspond to Mat4.m00..m33 in row order.
  All twelve cached minors, six determinant terms and sixteen output numerators
  are copied from that C contract, not from a foreign matrix convention.
  These proofs exclude IEEE rounding/underflow, singular division, conditioning,
  and trapping FP environments. Nonzero means the EXACT determinant expression.
-/
import GxMath.ClipMatrix

namespace GxMath.CofactorInverse
open GxMath.ClipMatrix

structure Minors where
  b00 : ℚ
  b01 : ℚ
  b02 : ℚ
  b03 : ℚ
  b04 : ℚ
  b05 : ℚ
  b06 : ℚ
  b07 : ℚ
  b08 : ℚ
  b09 : ℚ
  b10 : ℚ
  b11 : ℚ

def minors (m : Mat4) : Minors :=
  ⟨m.m00*m.m11-m.m01*m.m10, m.m00*m.m12-m.m02*m.m10,
   m.m00*m.m13-m.m03*m.m10, m.m01*m.m12-m.m02*m.m11,
   m.m01*m.m13-m.m03*m.m11, m.m02*m.m13-m.m03*m.m12,
   m.m20*m.m31-m.m21*m.m30, m.m20*m.m32-m.m22*m.m30,
   m.m20*m.m33-m.m23*m.m30, m.m21*m.m32-m.m22*m.m31,
   m.m21*m.m33-m.m23*m.m31, m.m22*m.m33-m.m23*m.m32⟩

def determinant (m : Mat4) : ℚ :=
  let b := minors m
  b.b00*b.b11-b.b01*b.b10+b.b02*b.b09+b.b03*b.b08-b.b04*b.b07+b.b05*b.b06

def adjugate (m : Mat4) : Mat4 :=
  let b := minors m
  { m00 := m.m11*b.b11-m.m12*b.b10+m.m13*b.b09,
    m01 := -m.m01*b.b11+m.m02*b.b10-m.m03*b.b09,
    m02 := m.m31*b.b05-m.m32*b.b04+m.m33*b.b03,
    m03 := -m.m21*b.b05+m.m22*b.b04-m.m23*b.b03,
    m10 := -m.m10*b.b11+m.m12*b.b08-m.m13*b.b07,
    m11 := m.m00*b.b11-m.m02*b.b08+m.m03*b.b07,
    m12 := -m.m30*b.b05+m.m32*b.b02-m.m33*b.b01,
    m13 := m.m20*b.b05-m.m22*b.b02+m.m23*b.b01,
    m20 := m.m10*b.b10-m.m11*b.b08+m.m13*b.b06,
    m21 := -m.m00*b.b10+m.m01*b.b08-m.m03*b.b06,
    m22 := m.m30*b.b04-m.m31*b.b02+m.m33*b.b00,
    m23 := -m.m20*b.b04+m.m21*b.b02-m.m23*b.b00,
    m30 := -m.m10*b.b09+m.m11*b.b07-m.m12*b.b06,
    m31 := m.m00*b.b09-m.m01*b.b07+m.m02*b.b06,
    m32 := -m.m30*b.b03+m.m31*b.b01-m.m32*b.b00,
    m33 := m.m20*b.b03-m.m21*b.b01+m.m22*b.b00 }

def scaleMatrix (m : Mat4) (k : ℚ) : Mat4 :=
  { m00 := m.m00*k, m01 := m.m01*k, m02 := m.m02*k, m03 := m.m03*k,
    m10 := m.m10*k, m11 := m.m11*k, m12 := m.m12*k, m13 := m.m13*k,
    m20 := m.m20*k, m21 := m.m21*k, m22 := m.m22*k, m23 := m.m23*k,
    m30 := m.m30*k, m31 := m.m31*k, m32 := m.m32*k, m33 := m.m33*k }

def inverse (m : Mat4) : Mat4 := scaleMatrix (adjugate m) (1/determinant m)

theorem laplace_row_zero (m : Mat4) :
    determinant m = m.m00*(adjugate m).m00 + m.m01*(adjugate m).m10 +
      m.m02*(adjugate m).m20 + m.m03*(adjugate m).m30 := by
  simp [determinant, adjugate, minors]
  ring

theorem matrix_adjugate_product (m : Mat4) :
    matMul m (adjugate m) = scaleMatrix matId (determinant m) := by
  ext <;> simp [matMul, adjugate, minors, scaleMatrix, matId, determinant] <;> ring

theorem adjugate_matrix_product (m : Mat4) :
    matMul (adjugate m) m = scaleMatrix matId (determinant m) := by
  ext <;> simp [matMul, adjugate, minors, scaleMatrix, matId, determinant] <;> ring

theorem multiply_scale_right (a b : Mat4) (k : ℚ) :
    matMul a (scaleMatrix b k) = scaleMatrix (matMul a b) k := by
  ext <;> simp [matMul, scaleMatrix] <;> ring

theorem multiply_scale_left (a b : Mat4) (k : ℚ) :
    matMul (scaleMatrix a k) b = scaleMatrix (matMul a b) k := by
  ext <;> simp [matMul, scaleMatrix] <;> ring

theorem reciprocal_scaled_identity (d : ℚ) (h : d ≠ 0) :
    scaleMatrix (scaleMatrix matId d) (1/d) = matId := by
  ext <;> simp [scaleMatrix, matId, h]

theorem inverse_product_right (m : Mat4) (h : determinant m ≠ 0) :
    matMul m (inverse m) = matId := by
  unfold inverse
  rw [multiply_scale_right, matrix_adjugate_product]
  exact reciprocal_scaled_identity _ h

theorem inverse_product_left (m : Mat4) (h : determinant m ≠ 0) :
    matMul (inverse m) m = matId := by
  unfold inverse
  rw [multiply_scale_left, adjugate_matrix_product]
  exact reciprocal_scaled_identity _ h

theorem inverse_identity : inverse matId = matId := by
  norm_num [inverse, scaleMatrix, adjugate, determinant, minors, matId]

--ai: total rational division at zero is NOT the C singular case or a useful inverse.
theorem singular_zero_not_inverse :
    determinant matZero = 0 ∧ inverse matZero = matZero ∧ matMul matZero (inverse matZero) ≠ matId := by
  norm_num [determinant, minors, inverse, adjugate, scaleMatrix, matMul, matZero, matId]

end GxMath.CofactorInverse
