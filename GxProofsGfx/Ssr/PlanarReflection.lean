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
  //ai: exact-rational plane reflection matching Draw_Reflections and planarSampleUV.
  Unit normal, nondegenerate LookAt frame, positive clip w and IEEE/GPU accuracy
  are distinct obligations. This does not certify SSR traversal or mirror feedback.
-/
import GxProofsGfx.Temporal.TemporalMatrix

namespace GxProofsGfx.PlanarReflection
open GxMath.ClipMatrix

def dot (n p : Vec4) : ℚ := n.x*p.x+n.y*p.y+n.z*p.z
def signed (n : Vec4) (d : ℚ) (p : Vec4) : ℚ := dot n p-d*p.w
def reflect (n : Vec4) (d : ℚ) (p : Vec4) : Vec4 :=
  ⟨p.x-2*(signed n d p)*n.x,p.y-2*(signed n d p)*n.y,
   p.z-2*(signed n d p)*n.z,p.w⟩

def distanceSq (a b : Vec4) : ℚ :=
  (a.x-b.x)^2+(a.y-b.y)^2+(a.z-b.z)^2

theorem preserves_homogeneous_w (n p : Vec4) (d : ℚ) : (reflect n d p).w = p.w := rfl

theorem direction_ignores_offset (n v : Vec4) (d : ℚ) (hv : v.w = 0) :
    reflect n d v = reflect n 0 v := by
  ext <;> simp [reflect, signed, hv]

theorem on_plane_fixed (n p : Vec4) (d : ℚ) (h : signed n d p = 0) :
    reflect n d p = p := by
  ext <;> simp [reflect, h]

theorem signed_distance_negated (n p : Vec4) (d : ℚ) (hn : dot n n = 1) :
    signed n d (reflect n d p) = -signed n d p := by
  simp only [signed, reflect, dot] at *
  linear_combination -2*(n.x*p.x+n.y*p.y+n.z*p.z-d*p.w)*hn

theorem reflection_involution (n p : Vec4) (d : ℚ) (hn : dot n n = 1) :
    reflect n d (reflect n d p) = p := by
  have hs := signed_distance_negated n p d hn
  ext
  · change (reflect n d p).x-2*(signed n d (reflect n d p))*n.x = p.x
    rw [hs]
    simp only [reflect]
    ring
  · change (reflect n d p).y-2*(signed n d (reflect n d p))*n.y = p.y
    rw [hs]
    simp only [reflect]
    ring
  · change (reflect n d p).z-2*(signed n d (reflect n d p))*n.z = p.z
    rw [hs]
    simp only [reflect]
    ring
  · rfl

theorem point_distances_preserved (n a b : Vec4) (d : ℚ) (hn : dot n n = 1)
    (ha : a.w = 1) (hb : b.w = 1) :
    distanceSq (reflect n d a) (reflect n d b) = distanceSq a b := by
  simp only [distanceSq, reflect, signed, ha, hb]
  unfold dot at *
  linear_combination 4*(n.x*(a.x-b.x)+n.y*(a.y-b.y)+n.z*(a.z-b.z))^2*hn

--ai: homogeneous row-action matrix, translation only in the last numeric row.
def reflectionMatrix (n : Vec4) (d : ℚ) : Mat4 :=
  { m00 := 1-2*n.x*n.x, m01 := -2*n.x*n.y, m02 := -2*n.x*n.z, m03 := 0,
    m10 := -2*n.y*n.x, m11 := 1-2*n.y*n.y, m12 := -2*n.y*n.z, m13 := 0,
    m20 := -2*n.z*n.x, m21 := -2*n.z*n.y, m22 := 1-2*n.z*n.z, m23 := 0,
    m30 := 2*d*n.x, m31 := 2*d*n.y, m32 := 2*d*n.z, m33 := 1 }

theorem reflection_matrix_action (n p : Vec4) (d : ℚ) :
    rowMul p (reflectionMatrix n d) = reflect n d p := by
  ext <;> simp [rowMul, reflectionMatrix, reflect, signed, dot] <;> ring

--ai: physical GL_TRUE upload and C view-then-projection composition, not a LookAt correctness proof.
theorem uploaded_reflection_projection (n p : Vec4) (d : ℚ) (view projection : Mat4) :
    colMul (TemporalMatrix.upload true (matMul view projection)) (reflect n d p) =
      rowMul (rowMul p (matMul (reflectionMatrix n d) view)) projection := by
  rw [TemporalMatrix.raw_upload_row_action, ← reflection_matrix_action, ← rowMul_matMul, ← rowMul_matMul]
  rw [matMul_assoc]

def projectedU (p : Vec4) : ℚ := (p.x/p.w+1)/2
def projectedV (p : Vec4) : ℚ := (p.y/p.w+1)/2

theorem on_plane_ssr_clip (n p : Vec4) (d : ℚ) (vp : Mat4) (h : signed n d p = 0) :
    rowMul (reflect n d p) vp = rowMul p vp := by rw [on_plane_fixed n p d h]

--ai: SSR has a positive-w gate; direct standard shader clamps w, agreeing only above its floor.
theorem direct_and_ssr_projection_agree (p : Vec4) (h : (1/1000 : ℚ) < p.w) :
    ((p.x / max p.w (1/10000)+1)/2, (p.y / max p.w (1/10000)+1)/2) =
      (projectedU p, projectedV p) := by
  have floor : (1/10000 : ℚ) ≤ p.w := by linarith
  rw [max_eq_left floor]
  rfl

theorem asymmetric_uv_witness :
    projectedU ⟨2,1,0,4⟩ = 3/4 ∧ projectedV ⟨2,1,0,4⟩ = 5/8 ∧
      1-projectedV ⟨2,1,0,4⟩ ≠ projectedV ⟨2,1,0,4⟩ := by
  norm_num [projectedU, projectedV]

theorem nonunit_normal_not_involution :
    reflect ⟨2,0,0,0⟩ 0 (reflect ⟨2,0,0,0⟩ 0 ⟨1,0,0,1⟩) ≠ ⟨1,0,0,1⟩ := by
  intro h
  have hx := congrArg Vec4.x h
  norm_num [reflect, signed, dot] at hx

end GxProofsGfx.PlanarReflection
