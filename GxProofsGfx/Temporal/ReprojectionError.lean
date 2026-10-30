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
  //ai: exact-rational residual-to-reprojection bounds, not IEEE certification.
  Residual entries, input vector norms, homogeneous margins and GPU/measurement
  error budgets are supplied hypotheses. The .05 pixel/.0005 depth witnesses
  illustrate the existing native budgets; they do not certify engine cameras.
-/
import GxProofsGfx.Temporal.CofactorInverse

namespace GxProofsGfx.ReprojectionError
open GxMath.ClipMatrix

def vectorSub (a b : Vec4) : Vec4 := ⟨a.x-b.x,a.y-b.y,a.z-b.z,a.w-b.w⟩
def matrixSub (a b : Mat4) : Mat4 :=
  { m00 := a.m00-b.m00, m01 := a.m01-b.m01, m02 := a.m02-b.m02, m03 := a.m03-b.m03,
    m10 := a.m10-b.m10, m11 := a.m11-b.m11, m12 := a.m12-b.m12, m13 := a.m13-b.m13,
    m20 := a.m20-b.m20, m21 := a.m21-b.m21, m22 := a.m22-b.m22, m23 := a.m23-b.m23,
    m30 := a.m30-b.m30, m31 := a.m31-b.m31, m32 := a.m32-b.m32, m33 := a.m33-b.m33 }

def residual (current candidate : Mat4) : Mat4 := matrixSub (matMul current candidate) matId
def VectorBound (v : Vec4) (bound : ℚ) : Prop :=
  |v.x| ≤ bound ∧ |v.y| ≤ bound ∧ |v.z| ≤ bound ∧ |v.w| ≤ bound
def EntryBound (m : Mat4) (bound : ℚ) : Prop :=
  |m.m00| ≤ bound ∧ |m.m01| ≤ bound ∧ |m.m02| ≤ bound ∧ |m.m03| ≤ bound ∧
  |m.m10| ≤ bound ∧ |m.m11| ≤ bound ∧ |m.m12| ≤ bound ∧ |m.m13| ≤ bound ∧
  |m.m20| ≤ bound ∧ |m.m21| ≤ bound ∧ |m.m22| ≤ bound ∧ |m.m23| ≤ bound ∧
  |m.m30| ≤ bound ∧ |m.m31| ≤ bound ∧ |m.m32| ≤ bound ∧ |m.m33| ≤ bound

theorem residual_action (world : Vec4) (current candidate : Mat4) :
    vectorSub (rowMul (rowMul world current) candidate) world = rowMul world (residual current candidate) := by
  rw [← rowMul_matMul]
  ext <;> simp [vectorSub, rowMul, residual, matrixSub, matId] <;> ring

theorem exact_cofactor_zero_residual (m : Mat4)
    (h : GxMath.CofactorInverse.determinant m ≠ 0) :
    residual m (GxMath.CofactorInverse.inverse m) = matZero := by
  rw [residual, GxMath.CofactorInverse.inverse_product_right m h]
  ext <;> simp [matrixSub, matId, matZero]

theorem abs_product_bound (a b w e : ℚ) (hw : 0 ≤ w) (ha : |a| ≤ w) (hb : |b| ≤ e) :
    |a*b| ≤ w*e := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hw

theorem dot_four_bound (a b c d p q r s w e : ℚ) (hw : 0 ≤ w)
    (hv : |a| ≤ w ∧ |b| ≤ w ∧ |c| ≤ w ∧ |d| ≤ w)
    (hm : |p| ≤ e ∧ |q| ≤ e ∧ |r| ≤ e ∧ |s| ≤ e) :
    |a*p+b*q+c*r+d*s| ≤ 4*w*e := by
  have h1 := abs_product_bound a p w e hw hv.1 hm.1
  have h2 := abs_product_bound b q w e hw hv.2.1 hm.2.1
  have h3 := abs_product_bound c r w e hw hv.2.2.1 hm.2.2.1
  have h4 := abs_product_bound d s w e hw hv.2.2.2 hm.2.2.2
  have t1 := abs_add_le (a*p) (b*q)
  have t2 := abs_add_le (a*p+b*q) (c*r)
  have t3 := abs_add_le (a*p+b*q+c*r) (d*s)
  linarith

theorem row_action_bound (v : Vec4) (m : Mat4) (w e : ℚ) (hw : 0 ≤ w)
    (hv : VectorBound v w) (hm : EntryBound m e) : VectorBound (rowMul v m) (4*w*e) := by
  rcases hm with ⟨h00,h01,h02,h03,h10,h11,h12,h13,h20,h21,h22,h23,h30,h31,h32,h33⟩
  exact ⟨dot_four_bound _ _ _ _ _ _ _ _ w e hw hv ⟨h00,h10,h20,h30⟩,
    dot_four_bound _ _ _ _ _ _ _ _ w e hw hv ⟨h01,h11,h21,h31⟩,
    dot_four_bound _ _ _ _ _ _ _ _ w e hw hv ⟨h02,h12,h22,h32⟩,
    dot_four_bound _ _ _ _ _ _ _ _ w e hw hv ⟨h03,h13,h23,h33⟩⟩

theorem inverse_world_error_bound (world : Vec4) (current candidate : Mat4) (w e : ℚ)
    (hw : 0 ≤ w) (hv : VectorBound world w) (he : EntryBound (residual current candidate) e) :
    VectorBound (vectorSub (rowMul (rowMul world current) candidate) world) (4*w*e) := by
  rw [residual_action]
  exact row_action_bound world _ w e hw hv he

--ai: en/ed bound numerator/denominator errors; mu is a LOWER bound on the actual absolute denominator.
def ratioBudget (mu en ed idealRatio : ℚ) : ℚ := (en + |idealRatio| *ed)/mu
def projectionBudget (mu en ed idealRatio : ℚ) : ℚ := ratioBudget mu en ed idealRatio / 2
def pixelBudget (width mu en ed idealRatio : ℚ) : ℚ := width * projectionBudget mu en ed idealRatio

theorem ratio_perturbation (n d n0 d0 mu en ed : ℚ)
    (hmu : 0 < mu) (hd : mu ≤ |d|) (h0 : d0 ≠ 0)
    (hn : |n-n0| ≤ en) (he : |d-d0| ≤ ed) :
    |n/d-n0/d0| ≤ ratioBudget mu en ed (n0/d0) := by
  have dn : d ≠ 0 := by intro hz; simp [hz] at hd; linarith
  have identity : n/d-n0/d0 = ((n-n0)-(n0/d0)*(d-d0))/d := by
    field_simp
    ring
  have triangle := abs_sub (n-n0) ((n0/d0)*(d-d0))
  have product := mul_le_mul_of_nonneg_left he (abs_nonneg (n0/d0))
  have numerator : |(n-n0)-(n0/d0)*(d-d0)| ≤ en+|n0/d0| *ed := by
    rw [abs_mul] at triangle
    linarith
  have positiveNumerator : 0 ≤ en+|n0/d0| *ed := le_trans (abs_nonneg _) numerator
  rw [identity, abs_div]
  unfold ratioBudget
  exact le_trans (div_le_div_of_nonneg_right numerator (le_trans (le_of_lt hmu) hd))
    (div_le_div_of_nonneg_left positiveNumerator hmu hd)

theorem normalized_world_error (world recovered : Vec4) (w e mu : ℚ)
    (hw : 0 ≤ w) (he : 0 ≤ e) (hmu : 0 < mu) (hd : mu ≤ |recovered.w|)
    (hunit : world.w = 1) (hv : VectorBound world w)
    (herr : VectorBound (vectorSub recovered world) (4*w*e)) :
    VectorBound (vectorSub (TemporalMatrix.normalize recovered) world) ((4*w*e+w*(4*w*e))/mu) := by
  have rn : recovered.w ≠ 0 := by intro hz; simp [hz] at hd; linarith
  have coordinate (a a0 : ℚ) (ha : |a-a0| ≤ 4*w*e) (ha0 : |a0| ≤ w) :
      |a/recovered.w-a0| ≤ (4*w*e+w*(4*w*e))/mu := by
    have ratio := ratio_perturbation a recovered.w a0 1 mu (4*w*e) (4*w*e)
      hmu hd (by norm_num) ha (by simpa [vectorSub, hunit] using herr.2.2.2)
    have hk : 0 ≤ 4*w*e := mul_nonneg (mul_nonneg (by norm_num) hw) he
    have magnitude := mul_le_mul_of_nonneg_right ha0 hk
    simp only [div_one, ratioBudget] at ratio
    exact le_trans ratio (div_le_div_of_nonneg_right (by linarith) (le_of_lt hmu))
  refine ⟨?_,?_,?_,?_⟩
  · simpa [TemporalMatrix.normalize, TemporalMatrix.scale, vectorSub, div_eq_mul_inv] using coordinate recovered.x world.x (by simpa [vectorSub] using herr.1) hv.1
  · simpa [TemporalMatrix.normalize, TemporalMatrix.scale, vectorSub, div_eq_mul_inv] using coordinate recovered.y world.y (by simpa [vectorSub] using herr.2.1) hv.2.1
  · simpa [TemporalMatrix.normalize, TemporalMatrix.scale, vectorSub, div_eq_mul_inv] using coordinate recovered.z world.z (by simpa [vectorSub] using herr.2.2.1) hv.2.2.1
  · simp [TemporalMatrix.normalize, TemporalMatrix.scale, vectorSub, rn, hunit]
    positivity

--ai: the shader normalizes clip before inverse multiplication; exact homogeneous scaling cancels.
theorem shader_normalization_equiv (world : Vec4) (current candidate : Mat4)
    (hc : (rowMul world current).w ≠ 0)
    (hr : (rowMul (rowMul world current) candidate).w ≠ 0) :
    TemporalMatrix.normalize (colMul (TemporalMatrix.upload true candidate)
      (TemporalMatrix.normalize (rowMul world current))) =
      TemporalMatrix.normalize (rowMul (rowMul world current) candidate) := by
  rw [TemporalMatrix.raw_upload_row_action]
  change TemporalMatrix.normalize
      (rowMul (TemporalMatrix.scale (rowMul world current) (1/(rowMul world current).w)) candidate) = _
  rw [TemporalMatrix.row_action_scale]
  exact TemporalMatrix.normalize_scale _ _ hr (one_div_ne_zero hc)

theorem shader_world_error_bound (world : Vec4) (current candidate : Mat4) (w e mu : ℚ)
    (hw : 0 ≤ w) (he : 0 ≤ e) (hmu : 0 < mu)
    (hd : mu ≤ |(rowMul (rowMul world current) candidate).w|)
    (hunit : world.w = 1) (hv : VectorBound world w)
    (herr : EntryBound (residual current candidate) e) (hc : (rowMul world current).w ≠ 0) :
    VectorBound (vectorSub (TemporalMatrix.normalize
      (colMul (TemporalMatrix.upload true candidate) (TemporalMatrix.normalize (rowMul world current)))) world)
      ((4*w*e+w*(4*w*e))/mu) := by
  have hr : (rowMul (rowMul world current) candidate).w ≠ 0 := by
    intro hz
    simp [hz] at hd
    linarith
  rw [shader_normalization_equiv world current candidate hc hr]
  exact normalized_world_error world _ w e mu hw he hmu hd hunit hv
    (inverse_world_error_bound world current candidate w e hw hv herr)

theorem previous_clip_error (actual ideal : Vec4) (previous : Mat4) (delta p : ℚ)
    (hd : 0 ≤ delta) (hv : VectorBound (vectorSub actual ideal) delta) (hp : EntryBound previous p) :
    VectorBound (vectorSub (rowMul actual previous) (rowMul ideal previous)) (4*delta*p) := by
  have linear : vectorSub (rowMul actual previous) (rowMul ideal previous) =
      rowMul (vectorSub actual ideal) previous := by
    ext <;> simp [vectorSub, rowMul] <;> ring
  rw [linear]
  exact row_action_bound _ previous delta p hd hv hp

theorem projection_perturbation (n d n0 d0 mu en ed : ℚ)
    (hmu : 0 < mu) (hd : mu ≤ |d|) (h0 : d0 ≠ 0)
    (hn : |n-n0| ≤ en) (he : |d-d0| ≤ ed) :
    |TemporalSampling.project n d-TemporalSampling.project n0 d0| ≤ projectionBudget mu en ed (n0/d0) := by
  have identity : TemporalSampling.project n d-TemporalSampling.project n0 d0 = (n/d-n0/d0)/2 := by
    unfold TemporalSampling.project
    ring
  rw [identity, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  exact div_le_div_of_nonneg_right (ratio_perturbation n d n0 d0 mu en ed hmu hd h0 hn he) (by norm_num)

--ai: measurement uncertainty is a supplied bound; double residual measurements are not exact certificates.
def reconstruct (world : Vec4) (current candidate : Mat4) : Vec4 :=
  TemporalMatrix.normalize (colMul (TemporalMatrix.upload true candidate)
    (TemporalMatrix.normalize (rowMul world current)))

def worldBudget (w e mu : ℚ) : ℚ := (4*w*e+w*(4*w*e))/mu

--ai: one bound covers previous U, V and projected depth before storage/evaluation uncertainty.
theorem residual_to_previous_projection (world : Vec4) (current candidate previous : Mat4)
    (w e mu p nu : ℚ) (hw : 0 ≤ w) (he : 0 ≤ e) (hmu : 0 < mu)
    (hd : mu ≤ |(rowMul (rowMul world current) candidate).w|)
    (hunit : world.w = 1) (hv : VectorBound world w)
    (herr : EntryBound (residual current candidate) e)
    (hc : (rowMul world current).w ≠ 0) (hp : EntryBound previous p)
    (hnu : 0 < nu) (hprev : nu ≤ |(rowMul (reconstruct world current candidate) previous).w|)
    (hideal : (rowMul world previous).w ≠ 0) :
    let actual := rowMul (reconstruct world current candidate) previous
    let ideal := rowMul world previous
    let k := 4 * worldBudget w e mu * p
    |TemporalSampling.project actual.x actual.w-TemporalSampling.project ideal.x ideal.w| ≤
      projectionBudget nu k k (ideal.x/ideal.w) ∧
    |TemporalSampling.project actual.y actual.w-TemporalSampling.project ideal.y ideal.w| ≤
      projectionBudget nu k k (ideal.y/ideal.w) ∧
    |TemporalSampling.project actual.z actual.w-TemporalSampling.project ideal.z ideal.w| ≤
      projectionBudget nu k k (ideal.z/ideal.w) := by
  have hb : 0 ≤ worldBudget w e mu := by unfold worldBudget; positivity
  have worldError := shader_world_error_bound world current candidate w e mu hw he hmu hd hunit hv herr hc
  have clipError := previous_clip_error (reconstruct world current candidate) world previous
    (worldBudget w e mu) p hb worldError hp
  exact ⟨projection_perturbation _ _ _ _ _ _ _ hnu hprev hideal clipError.1 clipError.2.2.2,
    projection_perturbation _ _ _ _ _ _ _ hnu hprev hideal clipError.2.1 clipError.2.2.2,
    projection_perturbation _ _ _ _ _ _ _ hnu hprev hideal clipError.2.2.1 clipError.2.2.2⟩

theorem projection_pixel_bound (n d n0 d0 width mu en ed : ℚ)
    (hw : 0 ≤ width) (hmu : 0 < mu) (hd : mu ≤ |d|) (h0 : d0 ≠ 0)
    (hn : |n-n0| ≤ en) (he : |d-d0| ≤ ed) :
    width * |TemporalSampling.project n d-TemporalSampling.project n0 d0| ≤
      pixelBudget width mu en ed (n0/d0) :=
  mul_le_mul_of_nonneg_left (projection_perturbation n d n0 d0 mu en ed hmu hd h0 hn he) hw

--ai: measurement uncertainty is a supplied bound; double residual measurements are not exact certificates.
theorem residual_measurement_margin (trueValue measuredValue measuredBound uncertainty : ℚ)
    (htrue : |trueValue-measuredValue| ≤ uncertainty) (hmeasured : |measuredValue| ≤ measuredBound) :
    |trueValue| ≤ measuredBound+uncertainty := by
  have triangle := abs_add_le (trueValue-measuredValue) measuredValue
  simp only [sub_add_cancel] at triangle
  linarith

--ai: observed includes GPU evaluation/storage error, which is never inferred from exact arithmetic.
theorem observed_budget (observed candidate ideal width bound uncertainty budget : ℚ)
    (hw : 0 ≤ width) (hc : width*|candidate-ideal| ≤ bound)
    (hg : width*|observed-candidate| ≤ uncertainty) (hb : bound+uncertainty ≤ budget) :
    width*|observed-ideal| ≤ budget := by
  have triangle := mul_le_mul_of_nonneg_left (abs_sub_le observed candidate ideal) hw
  linarith

theorem illustrative_pixel_budget : pixelBudget 640 2 (1/100000) (1/100000) (1/2) ≤ (1/20 : ℚ) := by
  norm_num [pixelBudget, projectionBudget, ratioBudget]

theorem illustrative_depth_budget :
    projectionBudget 2 (1/100000) (1/100000) (1/2) + 1/2048 ≤ (1/2000 : ℚ) := by
  norm_num [projectionBudget, ratioBudget]

theorem minimum_guard_alone_not_pixel_certificate :
    pixelBudget 640 (1/100000) (1/100000) (1/100000) (1/2) > (1/20 : ℚ) := by
  norm_num [pixelBudget, projectionBudget, ratioBudget]

--ai: an actual quotient-error witness, not just an overly conservative bound.
theorem small_denominator_error_witness :
    |(0 : ℚ)-1/100000| ≤ 1/100000 ∧
    |(1/100000 : ℚ)-1/100000| ≤ 1/100000 ∧
    640 * |TemporalSampling.project 0 (1/100000)-TemporalSampling.project (1/100000) (1/100000)| > (1/20 : ℚ) := by
  norm_num [TemporalSampling.project]

end GxProofsGfx.ReprojectionError
