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
  //ai: exact input sensitivity for the TAA clip constructor and history jitter.
  Depth format, nearest-rounding behavior, sampling and GPU evaluation remain
  separate obligations. UNORM examples do not certify the renderer texture.
-/
import GxProofsGfx.Temporal.WeightedReprojection

namespace GxProofsGfx.DepthInputError
open GxMath.ClipMatrix ReprojectionError WeightedReprojection

def shaderClip (u v jx jy depth : ℚ) : Vec4 :=
  ⟨2*u-1-jx, 2*v-1-jy, 2*depth-1, 1⟩

theorem clip_axis_error (u u0 j j0 eu ej : ℚ)
    (hu : |u-u0| ≤ eu) (hj : |j-j0| ≤ ej) :
    |(2*u-1-j)-(2*u0-1-j0)| ≤ 2*eu+ej := by
  have identity : (2*u-1-j)-(2*u0-1-j0) = 2*(u-u0)-(j-j0) := by ring
  rw [identity]
  have triangle := abs_sub (2*(u-u0)) (j-j0)
  have scale := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℚ) ≤ 2)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 2)] at triangle
  linarith

theorem shader_clip_error (u v jx jy d u0 v0 jx0 jy0 d0 eu ev ejx ejy ed : ℚ)
    (hu : |u-u0| ≤ eu) (hv : |v-v0| ≤ ev)
    (hx : |jx-jx0| ≤ ejx) (hy : |jy-jy0| ≤ ejy) (hd : |d-d0| ≤ ed) :
    ComponentBound (vectorSub (shaderClip u v jx jy d) (shaderClip u0 v0 jx0 jy0 d0))
      ⟨2*eu+ejx,2*ev+ejy,2*ed,0⟩ := by
  refine ⟨clip_axis_error _ _ _ _ _ _ hu hx,clip_axis_error _ _ _ _ _ _ hv hy,?_,?_⟩
  · have identity : (2*d-1)-(2*d0-1) = 2*(d-d0) := by ring
    change |(2*d-1)-(2*d0-1)| ≤ 2*ed
    rw [identity, abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
    exact mul_le_mul_of_nonneg_left hd (by norm_num)
  · simp [vectorSub, shaderClip]

def normalizationBudget (reference b : Vec4) (mu : ℚ) : Vec4 :=
  ⟨ratioBudget mu b.x b.w (reference.x/reference.w),
   ratioBudget mu b.y b.w (reference.y/reference.w),
   ratioBudget mu b.z b.w (reference.z/reference.w),0⟩

theorem normalized_input_error (actual reference b : Vec4) (mu : ℚ)
    (hmu : 0 < mu) (ha : mu ≤ |actual.w|) (hr : reference.w ≠ 0)
    (h : ComponentBound (vectorSub actual reference) b) :
    ComponentBound (vectorSub (TemporalMatrix.normalize actual) (TemporalMatrix.normalize reference))
      (normalizationBudget reference b mu) := by
  have hn : actual.w ≠ 0 := by intro hz; simp [hz] at ha; linarith
  refine ⟨?_,?_,?_,?_⟩
  · simpa [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizationBudget, div_eq_mul_inv]
      using ratio_perturbation actual.x actual.w reference.x reference.w mu b.x b.w hmu ha hr h.1 h.2.2.2
  · simpa [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizationBudget, div_eq_mul_inv]
      using ratio_perturbation actual.y actual.w reference.y reference.w mu b.y b.w hmu ha hr h.2.1 h.2.2.2
  · simpa [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizationBudget, div_eq_mul_inv]
      using ratio_perturbation actual.z actual.w reference.z reference.w mu b.z b.w hmu ha hr h.2.2.1 h.2.2.2
  · simp [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizationBudget, hn, hr]

def inputWorldBudget (referenceClip inputBound : Vec4) (candidate : Mat4) (mu : ℚ) : Vec4 :=
  normalizationBudget (rowMul referenceClip candidate) (weightedAction inputBound candidate) mu

theorem inverse_input_error (actualClip referenceClip inputBound : Vec4) (candidate : Mat4) (mu : ℚ)
    (h : ComponentBound (vectorSub actualClip referenceClip) inputBound)
    (hmu : 0 < mu) (ha : mu ≤ |(rowMul actualClip candidate).w|)
    (hr : (rowMul referenceClip candidate).w ≠ 0) :
    ComponentBound (vectorSub (TemporalMatrix.normalize (rowMul actualClip candidate))
      (TemporalMatrix.normalize (rowMul referenceClip candidate)))
      (inputWorldBudget referenceClip inputBound candidate mu) :=
  normalized_input_error _ _ _ mu hmu ha hr (weighted_previous_clip actualClip referenceClip inputBound candidate h)

def addBudget (a b : Vec4) : Vec4 := ⟨a.x+b.x,a.y+b.y,a.z+b.z,a.w+b.w⟩

--ai: add input sensitivity to an independently established baseline inverse-residual bound.
theorem combine_errors (actual baseline ideal a b : Vec4)
    (ha : ComponentBound (vectorSub actual baseline) a)
    (hb : ComponentBound (vectorSub baseline ideal) b) :
    ComponentBound (vectorSub actual ideal) (addBudget a b) := by
  have coordinate (x y z ax bx : ℚ) (h1 : |x-y| ≤ ax) (h2 : |y-z| ≤ bx) : |x-z| ≤ ax+bx :=
    le_trans (abs_sub_le x y z) (add_le_add h1 h2)
  exact ⟨coordinate _ _ _ _ _ ha.1 hb.1,coordinate _ _ _ _ _ ha.2.1 hb.2.1,
    coordinate _ _ _ _ _ ha.2.2.1 hb.2.2.1,coordinate _ _ _ _ _ ha.2.2.2 hb.2.2.2⟩

theorem input_to_previous_projection (actualClip referenceClip inputBound : Vec4)
    (candidate previous : Mat4) (mu nu : ℚ)
    (h : ComponentBound (vectorSub actualClip referenceClip) inputBound)
    (hmu : 0 < mu) (ha : mu ≤ |(rowMul actualClip candidate).w|)
    (hr : (rowMul referenceClip candidate).w ≠ 0)
    (hnu : 0 < nu)
    (hp : nu ≤ |(rowMul (TemporalMatrix.normalize (rowMul actualClip candidate)) previous).w|)
    (hi : (rowMul (TemporalMatrix.normalize (rowMul referenceClip candidate)) previous).w ≠ 0) :
    let actual := rowMul (TemporalMatrix.normalize (rowMul actualClip candidate)) previous
    let ideal := rowMul (TemporalMatrix.normalize (rowMul referenceClip candidate)) previous
    let b := weightedAction (inputWorldBudget referenceClip inputBound candidate mu) previous
    |TemporalSampling.project actual.x actual.w-TemporalSampling.project ideal.x ideal.w| ≤ projectionBudget nu b.x b.w (ideal.x/ideal.w) ∧
    |TemporalSampling.project actual.y actual.w-TemporalSampling.project ideal.y ideal.w| ≤ projectionBudget nu b.y b.w (ideal.y/ideal.w) ∧
    |TemporalSampling.project actual.z actual.w-TemporalSampling.project ideal.z ideal.w| ≤ projectionBudget nu b.z b.w (ideal.z/ideal.w) := by
  have hc := weighted_previous_clip _ _ _ previous
    (inverse_input_error actualClip referenceClip inputBound candidate mu h hmu ha hr)
  exact ⟨projection_perturbation _ _ _ _ _ _ _ hnu hp hi hc.1 hc.2.2.2,
    projection_perturbation _ _ _ _ _ _ _ hnu hp hi hc.2.1 hc.2.2.2,
    projection_perturbation _ _ _ _ _ _ _ hnu hp hi hc.2.2.1 hc.2.2.2⟩

--ai: nearest grid rounding is a HYPOTHESIS; no texture format or driver rounding is inferred.
theorem nearest_grid_depth (depth index levels : ℚ) (hn : 0 < levels)
    (hround : |index-levels*depth| ≤ 1/2) :
    |index/levels-depth| ≤ 1/(2*levels) := by
  have identity : index/levels-depth = (index-levels*depth)/levels := by
    field_simp <;> ring
  rw [identity, abs_div, abs_of_pos hn]
  have bound := div_le_div_of_nonneg_right hround (le_of_lt hn)
  convert bound using 1 <;> ring

theorem previous_jitter_error (u u0 j j0 eu ej : ℚ)
    (hu : |u-u0| ≤ eu) (hj : |j-j0| ≤ ej) :
    |(u+j/2)-(u0+j0/2)| ≤ eu+ej/2 := by
  have identity : (u+j/2)-(u0+j0/2) = (u-u0)+(j-j0)/2 := by ring
  rw [identity]
  have triangle := abs_add_le (u-u0) ((j-j0)/2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)] at triangle
  have bound := div_le_div_of_nonneg_right hj (by norm_num : (0 : ℚ) ≤ 2)
  linarith

theorem illustrative_unorm24_depth_budget :
    1/(2*(16777215 : ℚ)) < 1/2000 := by norm_num

end GxProofsGfx.DepthInputError
