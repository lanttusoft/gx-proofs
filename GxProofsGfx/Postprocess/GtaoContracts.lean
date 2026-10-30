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
  //ai: GTAO reconstruction, horizon update and red-channel blur contracts.
  Normalization, transcendental integration, GPU precision and pow external.
-/
import GxProofsGfx.Renderer.CsmContracts

namespace GxProofsGfx.GtaoContracts
open GxMath.ClipMatrix TemporalMatrix

def clipFromTexture (u v depth : ℚ) : Vec4 := ⟨2*u-1,2*v-1,2*depth-1,1⟩
def textureFromClip (clip : Vec4) : Vec4 :=
  ⟨(clip.x/clip.w+1)/2,(clip.y/clip.w+1)/2,(clip.z/clip.w+1)/2,1⟩

theorem texture_clip_identity (clip : Vec4) (hw : clip.w ≠ 0) :
    clipFromTexture (textureFromClip clip).x (textureFromClip clip).y (textureFromClip clip).z = TemporalMatrix.normalize clip := by
  ext <;> simp [clipFromTexture,textureFromClip,TemporalMatrix.normalize,scale] <;> field_simp <;> ring

theorem view_reconstruction (projection inverse : Mat4) (view : Vec4)
    (hi : matMul projection inverse = matId) (hv : view.w = 1)
    (hc : (rowMul view projection).w ≠ 0) :
    TemporalMatrix.normalize (colMul (upload true inverse)
      (clipFromTexture (textureFromClip (rowMul view projection)).x
        (textureFromClip (rowMul view projection)).y
        (textureFromClip (rowMul view projection)).z)) = view := by
  rw [texture_clip_identity _ hc]
  exact ideal_world_reconstruction projection inverse view hi hv hc

theorem screen_flip_involution (v : ℚ) : 1-(1-v) = v := by ring
theorem sample_double_flip_negative : (1 : ℚ)-3/4 ≠ 3/4 := by norm_num

--ai: selected texel index is supplied; this does not prove GLSL floor or sampler tie behavior.
def texelCenter (index size : ℚ) : ℚ := (index+1/2)/size
theorem texel_center_error (index size uv : ℚ) (hn : 0 < size)
    (hl : index ≤ uv*size) (hu : uv*size ≤ index+1) :
    |uv-texelCenter index size| ≤ (1/2)/size := by
  apply abs_le.mpr
  unfold texelCenter
  constructor
  · have h : -(1/2)/size ≤ uv-(index+1/2)/size := by
      apply (div_le_iff₀ hn).mpr
      field_simp
      linarith
    simpa [neg_div] using h
  · apply (le_div_iff₀ hn).mpr
    field_simp
    linarith

theorem planar_sample_coordinate_mismatch (uv center slope offset : ℚ) :
    (slope*center+offset)-(slope*uv+offset) = slope*(center-uv) := by ring

theorem coherent_planar_sample (center slope offset : ℚ) :
    (slope*center+offset)-(slope*center+offset) = 0 := by ring

def stepDistance (radius fraction step : ℚ) : ℚ := radius*(step+fraction)/6
theorem stratified_step_spacing (radius fraction step : ℚ) :
    stepDistance radius fraction (step+1)-stepDistance radius fraction step = radius/6 := by
  unfold stepDistance
  ring

theorem stratified_last_step (radius fraction : ℚ) (hr : 0 ≤ radius)
    (hf : 0 ≤ fraction ∧ fraction < 1) :
    radius*5/6 ≤ stepDistance radius fraction 5 ∧ stepDistance radius fraction 5 ≤ radius := by
  unfold stepDistance
  have hl := mul_nonneg hr hf.1
  have hu := mul_le_mul_of_nonneg_left (le_of_lt hf.2) hr
  constructor <;> nlinarith

theorem collapsed_old_schedule_negative :
    (1 : ℚ)*(1/100)*(6/6) < stepDistance 1 (1/100) 5 := by
  norm_num [stepDistance]

--ai: the exact threshold models ideal 0.999, not its binary32 literal rounding.
def background (depth : ℚ) : Prop := 999/1000 ≤ depth
theorem clear_is_background : background 1 := by norm_num [background]
theorem near_far_geometry_can_be_background : background (9995/10000) := by norm_num [background]

def horizon (h sample weight : ℚ) : ℚ := h+max 0 (sample-h)*weight
theorem horizon_nondecreasing (h sample weight : ℚ) (hw : 0 ≤ weight) : h ≤ horizon h sample weight := by
  unfold horizon
  have := mul_nonneg (le_max_left (0 : ℚ) (sample-h)) hw
  linarith

theorem horizon_range (h sample weight : ℚ) (hh : -1 ≤ h ∧ h ≤ 1)
    (hs : -1 ≤ sample ∧ sample ≤ 1) (hw : 0 ≤ weight ∧ weight ≤ 1) :
    -1 ≤ horizon h sample weight ∧ horizon h sample weight ≤ 1 := by
  unfold horizon
  by_cases hc : sample ≤ h
  · rw [max_eq_left (by linarith)]
    simpa using hh
  · rw [max_eq_right (by linarith)]
    have hm := mul_nonneg (by linarith : 0 ≤ sample-h) hw.1
    have hu := mul_le_mul_of_nonneg_left hw.2 (by linarith : 0 ≤ sample-h)
    constructor <;> nlinarith [hh.1,hs.2]

theorem progressive_weight (step : ℕ) :
    0 < (2 : ℚ)/(step+2) ∧ (2 : ℚ)/(step+2) ≤ 1 := by
  have h : (0 : ℚ) ≤ step := Nat.cast_nonneg step
  constructor
  · exact div_pos (by norm_num) (by linarith)
  · rw [div_le_one (by linarith)]
    linarith

--ai: conditional planar stencil; arbitrary discontinuities can yield zero/wrong normals.
theorem planar_stencil_normal (dx dy : ℚ) :
    ReflectionHandedness.cross ⟨dx,0,0,0⟩ ⟨0,dy,0,0⟩ = ⟨0,0,dx*dy,0⟩ := by
  ext <;> simp [ReflectionHandedness.cross]

def eligibleSeparation (separation bias : ℚ) : Prop := max bias 0 < separation
theorem tangent_plane_rejected (bias : ℚ) : ¬ eligibleSeparation 0 bias := by
  unfold eligibleSeparation
  exact not_lt_of_ge (le_max_right _ _)

theorem biased_error_self_rejected (separation bias uncertainty : ℚ)
    (he : separation ≤ uncertainty) (hb : uncertainty ≤ max bias 0) :
    ¬ eligibleSeparation separation bias := by
  unfold eligibleSeparation
  exact not_lt_of_ge (le_trans he hb)

theorem weighted_blur_range (sum weight floor : ℚ) (hs : 0 ≤ sum) (hw : sum ≤ weight)
    (hf : 0 < floor) : 0 ≤ sum/max weight floor ∧ sum/max weight floor ≤ 1 := by
  have hd : 0 < max weight floor := lt_of_lt_of_le hf (le_max_right _ _)
  constructor
  · exact div_nonneg hs (le_of_lt hd)
  · rw [div_le_one hd]
    exact le_trans hw (le_max_left _ _)

theorem zero_blur_weight_dark : (0 : ℚ)/max 0 (1/1000) = 0 := by norm_num

end GxProofsGfx.GtaoContracts
