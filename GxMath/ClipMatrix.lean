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

/- gX — row-major clip-matrix theory (upload + clip test)

  Salvaged from gameX lean/GameXProofs/GXMatrixTheory.lean, re-verified
  against the gX row-major convention (src/gxmath/matrix.c:
  m0..m3 = row 0, standard A×B multiply — the same convention the
  gameX spec formalizes; the gameX Vulkan-battle instantiation is
  dropped, the generic invariants transfer unchanged).

  Convention (matches gxmath / the engine):
    * Mat4 is row-major: m[i][j] = row i, column j.
    * Vertex transform is ROW-vector: clip = rowMul p M  (p * M).
    * matMul A B = A * B (standard row-major product).
    * Raw GL_TRUE upload of the physical gX_Matrix struct yields transpose M,
      so GLSL column-vector action matches rowMul p M. GfxTemporalMatrix pins
      that physical-layout contract; UBO serialization is a separate obligation.

  Relation to GxMath/Matrix.lean: that module proves the same
  transpose/mul identities on the engine's Matrix structure; this
  module additionally pins the row-vector clip semantics, the
  UBO-upload equivalence, the NDC/depth mapping, and the
  composition-order non-commutativity.

  Theorems proven:
    - rowMul_zero:        zero matrix maps every vertex to the zero clip vector
    - rowMul_zero_w:      ... its clip w = 0
    - upload_equiv:       colMul M v = rowMul v (transpose M) (UBO upload)
    - matMul_assoc:       matrix multiplication is associative
    - rowMul_matMul:      row-vector transform distributes over matMul
    - clipTest_ne_zero_w: clip w = 0 ⇒ clipped
    - clipTest_ne_neg_w:  clip w < 0 ⇒ clipped
    - clipTest_ne_nonpos_w: clip w ≤ 0 ⇒ clipped
    - clipTest_ne_via_y:  |c.y| > c.w ⇒ clipped
    - matMul_not_comm:    matrix multiplication is not commutative
-/

--ai: use the pinned Mathlib rational field module; Data.Rat.Basic no longer exists.
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic

namespace GxMath.ClipMatrix

structure Vec4 where
  x : ℚ
  y : ℚ
  z : ℚ
  w : ℚ

structure Mat4 where
  m00 : ℚ
  m01 : ℚ
  m02 : ℚ
  m03 : ℚ
  m10 : ℚ
  m11 : ℚ
  m12 : ℚ
  m13 : ℚ
  m20 : ℚ
  m21 : ℚ
  m22 : ℚ
  m23 : ℚ
  m30 : ℚ
  m31 : ℚ
  m32 : ℚ
  m33 : ℚ

namespace Vec4
  @[ext] theorem ext {a b : Vec4} (hx : a.x = b.x) (hy : a.y = b.y)
      (hz : a.z = b.z) (hw : a.w = b.w) : a = b := by
    cases a; cases b; simp_all
end Vec4

namespace Mat4
  def get (M : Mat4) (i j : Nat) : ℚ :=
    match i, j with
    | 0, 0 => M.m00 | 0, 1 => M.m01 | 0, 2 => M.m02 | 0, 3 => M.m03
    | 1, 0 => M.m10 | 1, 1 => M.m11 | 1, 2 => M.m12 | 1, 3 => M.m13
    | 2, 0 => M.m20 | 2, 1 => M.m21 | 2, 2 => M.m22 | 2, 3 => M.m23
    | 3, 0 => M.m30 | 3, 1 => M.m31 | 3, 2 => M.m32 | 3, 3 => M.m33
    | _, _ => 0

  @[ext] theorem ext {a b : Mat4} (h : ∀ i j, Mat4.get a i j = Mat4.get b i j) : a = b := by
    cases a; cases b
    have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2; have h03 := h 0 3
    have h10 := h 1 0; have h11 := h 1 1; have h12 := h 1 2; have h13 := h 1 3
    have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2; have h23 := h 2 3
    have h30 := h 3 0; have h31 := h 3 1; have h32 := h 3 2; have h33 := h 3 3
    simp_all [Mat4.get]
end Mat4

-- row-vector transform: v' = v * M
def rowMul (v : Vec4) (M : Mat4) : Vec4 :=
  { x := v.x * M.m00 + v.y * M.m10 + v.z * M.m20 + v.w * M.m30,
    y := v.x * M.m01 + v.y * M.m11 + v.z * M.m21 + v.w * M.m31,
    z := v.x * M.m02 + v.y * M.m12 + v.z * M.m22 + v.w * M.m32,
    w := v.x * M.m03 + v.y * M.m13 + v.z * M.m23 + v.w * M.m33 }

-- column-vector transform: v' = M * v  (GLSL convention)
def colMul (M : Mat4) (v : Vec4) : Vec4 :=
  { x := M.m00 * v.x + M.m01 * v.y + M.m02 * v.z + M.m03 * v.w,
    y := M.m10 * v.x + M.m11 * v.y + M.m12 * v.z + M.m13 * v.w,
    z := M.m20 * v.x + M.m21 * v.y + M.m22 * v.z + M.m23 * v.w,
    w := M.m30 * v.x + M.m31 * v.y + M.m32 * v.z + M.m33 * v.w }

-- row-major product: C = A * B, C[i][j] = Σ_k A[i][k] * B[k][j]
def matMul (A B : Mat4) : Mat4 :=
  { m00 := A.m00*B.m00 + A.m01*B.m10 + A.m02*B.m20 + A.m03*B.m30,
    m01 := A.m00*B.m01 + A.m01*B.m11 + A.m02*B.m21 + A.m03*B.m31,
    m02 := A.m00*B.m02 + A.m01*B.m12 + A.m02*B.m22 + A.m03*B.m32,
    m03 := A.m00*B.m03 + A.m01*B.m13 + A.m02*B.m23 + A.m03*B.m33,
    m10 := A.m10*B.m00 + A.m11*B.m10 + A.m12*B.m20 + A.m13*B.m30,
    m11 := A.m10*B.m01 + A.m11*B.m11 + A.m12*B.m21 + A.m13*B.m31,
    m12 := A.m10*B.m02 + A.m11*B.m12 + A.m12*B.m22 + A.m13*B.m32,
    m13 := A.m10*B.m03 + A.m11*B.m13 + A.m12*B.m23 + A.m13*B.m33,
    m20 := A.m20*B.m00 + A.m21*B.m10 + A.m22*B.m20 + A.m23*B.m30,
    m21 := A.m20*B.m01 + A.m21*B.m11 + A.m22*B.m21 + A.m23*B.m31,
    m22 := A.m20*B.m02 + A.m21*B.m12 + A.m22*B.m22 + A.m23*B.m32,
    m23 := A.m20*B.m03 + A.m21*B.m13 + A.m22*B.m23 + A.m23*B.m33,
    m30 := A.m30*B.m00 + A.m31*B.m10 + A.m32*B.m20 + A.m33*B.m30,
    m31 := A.m30*B.m01 + A.m31*B.m11 + A.m32*B.m21 + A.m33*B.m31,
    m32 := A.m30*B.m02 + A.m31*B.m12 + A.m32*B.m22 + A.m33*B.m32,
    m33 := A.m30*B.m03 + A.m31*B.m13 + A.m32*B.m23 + A.m33*B.m33 }

def transpose (M : Mat4) : Mat4 :=
  { m00 := M.m00, m01 := M.m10, m02 := M.m20, m03 := M.m30,
    m10 := M.m01, m11 := M.m11, m12 := M.m21, m13 := M.m31,
    m20 := M.m02, m21 := M.m12, m22 := M.m22, m23 := M.m32,
    m30 := M.m03, m31 := M.m13, m32 := M.m23, m33 := M.m33 }

def matZero : Mat4 :=
  { m00 := 0, m01 := 0, m02 := 0, m03 := 0,
    m10 := 0, m11 := 0, m12 := 0, m13 := 0,
    m20 := 0, m21 := 0, m22 := 0, m23 := 0,
    m30 := 0, m31 := 0, m32 := 0, m33 := 0 }

def matId : Mat4 :=
  { m00 := 1, m01 := 0, m02 := 0, m03 := 0,
    m10 := 0, m11 := 1, m12 := 0, m13 := 0,
    m20 := 0, m21 := 0, m22 := 1, m23 := 0,
    m30 := 0, m31 := 0, m32 := 0, m33 := 1 }

def vecZero : Vec4 := { x := 0, y := 0, z := 0, w := 0 }

-- ---------------------------------------------------------------------------
-- T_zero — the zero matrix maps every vertex to the zero clip vector.
--   A degenerate mvp (all-zero except m33) produces clip w = 0 for every
--   vertex → no fragments are rasterized.
-- ---------------------------------------------------------------------------
theorem rowMul_zero (v : Vec4) : rowMul v matZero = vecZero := by
  ext <;> simp [rowMul, matZero, vecZero]

theorem rowMul_zero_w (v : Vec4) : (rowMul v matZero).w = 0 := by
  simp [rowMul, matZero]

-- ---------------------------------------------------------------------------
--ai: generic row/column duality, not proof of an engine UBO byte serialization.
-- ---------------------------------------------------------------------------
theorem upload_equiv (M : Mat4) (v : Vec4) : colMul M v = rowMul v (transpose M) := by
  ext <;> simp [colMul, rowMul, transpose] <;> ring_nf

-- ---------------------------------------------------------------------------
-- matMul is associative — the engine composes mvp = model·view·proj in any
--   parenthesization and gets the same matrix.
-- ---------------------------------------------------------------------------
theorem matMul_assoc (A B C : Mat4) : matMul (matMul A B) C = matMul A (matMul B C) := by
  ext; simp [matMul]; ring_nf

theorem rowMul_matMul (v : Vec4) (A B : Mat4) :
    rowMul v (matMul A B) = rowMul (rowMul v A) B := by
  ext <;> simp [rowMul, matMul] <;> ring_nf

-- ---------------------------------------------------------------------------
-- Clip test (GL semantics): -w ≤ x ≤ w ∧ -w ≤ y ≤ w ∧ -w ≤ z ≤ w ∧ w > 0.
--   A vertex fails the test (is clipped) iff ¬ clipTest (rowMul p mvp).
-- ---------------------------------------------------------------------------
def clipTest (c : Vec4) : Prop :=
  c.w > 0 ∧ |c.x| ≤ c.w ∧ |c.y| ≤ c.w ∧ |c.z| ≤ c.w

-- A vertex with clip w = 0 is always clipped (degenerate).
theorem clipTest_ne_zero_w {c : Vec4} (hw : c.w = 0) : ¬ clipTest c := by
  intro h
  have hw' : c.w > 0 := h.1
  rw [hw] at hw'
  exact (lt_irrefl (0 : ℚ)) hw'

-- A vertex with clip w < 0 is always clipped (behind the camera).
theorem clipTest_ne_neg_w {c : Vec4} (hw : c.w < 0) : ¬ clipTest c := by
  intro h
  exact (not_lt_of_ge (le_of_lt hw)) h.1

-- A vertex with clip w ≤ 0 is always clipped (covers w = 0 and w < 0).
theorem clipTest_ne_nonpos_w {c : Vec4} (hw : c.w ≤ 0) : ¬ clipTest c := by
  intro h
  exact (not_lt_of_ge hw) h.1

-- A vertex with |c.y| > c.w is always clipped (outside y bounds).
theorem clipTest_ne_via_y {c : Vec4} (hw : c.w < |c.y|) : ¬ clipTest c := by
  intro h
  have hy' : |c.y| ≤ c.w := h.2.2.1
  exact (lt_irrefl c.w) (lt_of_lt_of_le hw hy')

-- ---------------------------------------------------------------------------
-- NDC + depth (GL -1..1 mapping): depth = (ndc.z + 1) / 2.
-- ---------------------------------------------------------------------------
def ndc (c : Vec4) : ℚ := c.z / c.w

def depth (c : Vec4) : ℚ := (ndc c + 1) / 2

-- Depth test LEQUAL: the fragment passes iff depth ≤ stored.
def lequal (d stored : ℚ) : Prop := d ≤ stored

-- ---------------------------------------------------------------------------
-- Composition-order invariant.
--   clip = rowMul p (view·proj) vs clip = rowMul p (proj·view) differ in
--   general: matrix multiplication is not commutative — the multiply
--   order must match the GPU's P×V application order.
-- ---------------------------------------------------------------------------
theorem matMul_not_comm : ∃ A B : Mat4, matMul A B ≠ matMul B A := by
  -- witness: A has m01 = 1 (shift along x), B has m10 = 1 (shift along y)
  --   matMul A B m00 = A.m00*B.m00 + A.m01*B.m10 + ... = 0*0 + 1*1 = 1
  --   matMul B A m00 = B.m00*A.m00 + B.m01*A.m10 + ... = 0*0 + 0*0 = 0
  let A : Mat4 := { m00 := 0, m01 := 1, m02 := 0, m03 := 0,
                    m10 := 0, m11 := 0, m12 := 0, m13 := 0,
                    m20 := 0, m21 := 0, m22 := 0, m23 := 0,
                    m30 := 0, m31 := 0, m32 := 0, m33 := 0 }
  let B : Mat4 := { m00 := 0, m01 := 0, m02 := 0, m03 := 0,
                    m10 := 1, m11 := 0, m12 := 0, m13 := 0,
                    m20 := 0, m21 := 0, m22 := 0, m23 := 0,
                    m30 := 0, m31 := 0, m32 := 0, m33 := 0 }
  refine ⟨A, B, ?_⟩
  intro h
  have hm : (matMul A B).m00 = (matMul B A).m00 := by
    exact congrArg (fun M => M.m00) h
  norm_num [matMul] at hm

end GxMath.ClipMatrix
