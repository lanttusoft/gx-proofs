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
  //ai: gX ideal temporal reprojection and base-level history sampling.
  Grounded in resources/shader/gfx_taa_resolve.frag.
  Rational arithmetic is exact: these are not IEEE/GLSL or matrix-upload proofs.
  Coordinates are componentwise after the shader's Y flip. The camera fallback
  assumes valid inverse VP, nonzero world homogeneous w, and previous w > 1e-5.
  Neither matrix inversion nor raster/texture synchronization is established.
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace GxProofsGfx.TemporalSampling

def project (component w : ℚ) : ℚ := component / w / 2 + 1 / 2
def unjitter (uv jitter : ℚ) : ℚ := uv * 2 - 1 - jitter
def fallbackVelocity (uv prevUV prevJitter : ℚ) : ℚ := uv - (prevUV + prevJitter / 2)
def historyUV (uv velocity : ℚ) : ℚ := uv - velocity
def motionVelocity (uv prevUV jitter prevJitter : ℚ) : ℚ :=
  fallbackVelocity uv prevUV prevJitter - (jitter - prevJitter) / 2

theorem rendered_clip_reconstruction (c w jitter : ℚ) :
    unjitter (project c w + jitter / 2) jitter = c / w := by
  unfold unjitter project
  ring

theorem homogeneous_scale_invariant (c w scale : ℚ) (hw : w ≠ 0) (hs : scale ≠ 0) :
    project (scale * c) (scale * w) = project c w := by
  unfold project
  field_simp

theorem fallback_samples_previous_jitter (uv prevUV prevJitter : ℚ) :
    historyUV uv (fallbackVelocity uv prevUV prevJitter) = prevUV + prevJitter / 2 := by
  unfold historyUV fallbackVelocity
  ring

theorem static_camera_motion_is_zero (baseUV jitter prevJitter : ℚ) :
    motionVelocity (baseUV + jitter / 2) baseUV jitter prevJitter = 0 := by
  unfold motionVelocity fallbackVelocity
  ring

--ai: History position and motion classification are different quantities.
theorem motion_is_unjittered_displacement (uv prevUV jitter prevJitter : ℚ) :
    motionVelocity uv prevUV jitter prevJitter = uv - jitter / 2 - prevUV := by
  unfold motionVelocity fallbackVelocity
  ring

theorem depth_range_iff_clip_range (z w : ℚ) (hw : 0 < w) :
    (0 ≤ project z w ∧ project z w ≤ 1) ↔ (-w ≤ z ∧ z ≤ w) := by
  unfold project
  constructor
  · intro h
    have lo : -1 ≤ z / w := by linarith [h.1]
    have hi : z / w ≤ 1 := by linarith [h.2]
    exact ⟨by simpa using (le_div_iff₀ hw).mp lo,
           by simpa using (div_le_iff₀ hw).mp hi⟩
  · intro h
    have lo : -1 ≤ z / w := (le_div_iff₀ hw).mpr (by simpa using h.1)
    have hi : z / w ≤ 1 := (div_le_iff₀ hw).mpr (by simpa using h.2)
    constructor <;> linarith

def mix (a b t : ℚ) : ℚ := (1 - t) * a + t * b
def bilinear (a b c d x y : ℚ) : ℚ := mix (mix a b x) (mix c d x) y

theorem weights_sum_to_one (x y : ℚ) :
    (1 - x) * (1 - y) + x * (1 - y) + (1 - x) * y + x * y = 1 := by ring

theorem weights_nonnegative (x y : ℚ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ (1 - x) * (1 - y) ∧ 0 ≤ x * (1 - y) ∧ 0 ≤ (1 - x) * y ∧ 0 ≤ x * y := by
  exact ⟨mul_nonneg (by linarith [hx.2]) (by linarith [hy.2]),
    mul_nonneg hx.1 (by linarith [hy.2]), mul_nonneg (by linarith [hx.2]) hy.1,
    mul_nonneg hx.1 hy.1⟩

theorem nested_mix_is_weighted_sum (a b c d x y : ℚ) :
    bilinear a b c d x y =
      (1-x)*(1-y)*a + x*(1-y)*b + (1-x)*y*c + x*y*d := by
  unfold bilinear mix
  ring

theorem mix_within_bounds (a b t lo hi : ℚ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ mix a b t ∧ mix a b t ≤ hi := by
  have w : 0 ≤ 1 - t := by linarith [ht.2]
  have al := mul_le_mul_of_nonneg_left ha.1 w
  have bl := mul_le_mul_of_nonneg_left hb.1 ht.1
  have ah := mul_le_mul_of_nonneg_left ha.2 w
  have bh := mul_le_mul_of_nonneg_left hb.2 ht.1
  unfold mix
  constructor <;> nlinarith

theorem bilinear_within_bounds (a b c d x y lo hi : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hc : lo ≤ c ∧ c ≤ hi) (hd : lo ≤ d ∧ d ≤ hi) :
    lo ≤ bilinear a b c d x y ∧ bilinear a b c d x y ≤ hi :=
  mix_within_bounds _ _ y lo hi hy
    (mix_within_bounds a b x lo hi hx ha hb) (mix_within_bounds c d x lo hi hx hc hd)

theorem constant_history_preserved (a x y : ℚ) : bilinear a a a a x y = a := by
  unfold bilinear mix
  ring

--ai: Each RGBA component uses the same taps and weights, including depth alpha.
theorem bilinear_depth_remains_normalized (a b c d x y : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
    0 ≤ bilinear a b c d x y ∧ bilinear a b c d x y ≤ 1 :=
  bilinear_within_bounds a b c d x y 0 1 hx hy ha hb hc hd

def pixelCoordinate (uv : ℚ) (size : ℤ) : ℚ := uv * size - 1 / 2
def clampIndex (index size : ℤ) : ℤ := min (max index 0) (size - 1)

theorem texel_center_coordinate (index size : ℤ) (hs : (size : ℚ) ≠ 0) :
    pixelCoordinate (((index : ℚ) + 1 / 2) / size) size = index := by
  unfold pixelCoordinate
  field_simp
  ring

theorem footprint_fraction_valid (uv : ℚ) (size : ℤ) :
    0 ≤ Int.fract (pixelCoordinate uv size) ∧ Int.fract (pixelCoordinate uv size) < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem clamped_tap_in_bounds (index size : ℤ) (hs : 0 < size) :
    0 ≤ clampIndex index size ∧ clampIndex index size < size := by
  unfold clampIndex
  omega

theorem singleton_texture_taps_zero (index : ℤ) : clampIndex index 1 = 0 := by
  unfold clampIndex
  omega

theorem left_edge_footprint :
    Int.floor (pixelCoordinate 0 4) = -1 ∧
    clampIndex (-1) 4 = 0 ∧ clampIndex 0 4 = 0 := by
  norm_num [pixelCoordinate, clampIndex]

theorem right_edge_footprint :
    Int.floor (pixelCoordinate 1 4) = 3 ∧
    clampIndex 3 4 = 3 ∧ clampIndex 4 4 = 3 := by
  norm_num [pixelCoordinate, clampIndex]

--ai: Closed UV edges are eligible; the explicit taps clamp indices, not UVs.
def inView (u v depth w : ℚ) : Prop :=
  1 / 100000 < w ∧ 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ 0 ≤ depth ∧ depth ≤ 1
def depthCompatible (sample expected : ℚ) : Prop := |sample - expected| ≤ 1 / 1000
def eligible (u v depth w coverage sample : ℚ) : Prop :=
  -(3 / 2) ≤ coverage ∧ inView u v depth w ∧ depthCompatible sample depth

theorem eligibility_matches_strict_shader_rejection (u v depth w coverage sample : ℚ) :
    eligible u v depth w coverage sample ↔
      ¬ (coverage < -(3 / 2) ∨ w ≤ 1 / 100000 ∨ u < 0 ∨ 1 < u ∨ v < 0 ∨ 1 < v ∨
          depth < 0 ∨ 1 < depth ∨ 1 / 1000 < |sample - depth|) := by
  unfold eligible inView depthCompatible
  push_neg
  tauto

theorem exact_depth_is_compatible (depth : ℚ) : depthCompatible depth depth := by
  norm_num [depthCompatible]

theorem strict_depth_mismatch_rejected (u v depth w coverage sample : ℚ)
    (h : 1 / 1000 < |sample - depth|) : ¬ eligible u v depth w coverage sample := by
  unfold eligible depthCompatible
  intro accepted
  linarith [accepted.2.2]

theorem clock_coverage_rejected (u v depth w sample : ℚ) : ¬ eligible u v depth w (-2) sample := by
  unfold eligible
  norm_num

theorem w_boundary_rejected (u v depth coverage sample : ℚ) :
    ¬ eligible u v depth (1 / 100000) coverage sample := by
  simp [eligible, inView]

theorem closed_uv_edges_eligible : eligible 0 1 (1/2) 1 (-1) (1/2) := by
  norm_num [eligible, inView, depthCompatible]

theorem exact_tolerance_is_compatible : depthCompatible (501/1000) (1/2) := by
  norm_num [depthCompatible]

--ai: Convex bounds and depth agreement alone cannot establish surface identity.
theorem interpolated_depth_can_match_without_matching_taps :
    bilinear 0 1 0 1 (1/2) (1/2) = (1/2 : ℚ) ∧
    depthCompatible (bilinear 0 1 0 1 (1/2) (1/2)) (1/2) ∧
    ¬ depthCompatible 0 (1/2) ∧ ¬ depthCompatible 1 (1/2) := by
  norm_num [bilinear, mix, depthCompatible]

--ai: Conditional error budgets, not measured bounds on half-float storage or division.
theorem depth_error_margin (sample expected idealSample idealExpected es ee : ℚ)
    (hs : |sample - idealSample| ≤ es) (he : |idealExpected - expected| ≤ ee)
    (margin : |idealSample - idealExpected| + es + ee ≤ 1 / 1000) :
    depthCompatible sample expected := by
  have first := abs_sub_le sample idealSample idealExpected
  have second := abs_sub_le sample idealExpected expected
  unfold depthCompatible
  linarith

--ai: finiteness is an explicit runtime classification input; rationals do not represent NaN/Inf.
def worldDivisionSafe (finite : Bool) (w : ℚ) : Prop :=
  finite = true ∧ 1/100000 < |w|
def previousDivisionSafe (finite : Bool) (w : ℚ) : Prop :=
  finite = true ∧ 1/100000 < w

theorem world_guard_nonzero (finite : Bool) (w : ℚ) (h : worldDivisionSafe finite w) : w ≠ 0 := by
  intro hz
  norm_num [worldDivisionSafe, hz] at h

theorem previous_guard_positive (finite : Bool) (w : ℚ) (h : previousDivisionSafe finite w) :
    0 < w := by
  unfold previousDivisionSafe at h
  linarith [h.2]

theorem nonfinite_world_rejected (w : ℚ) : ¬ worldDivisionSafe false w := by
  simp [worldDivisionSafe]

theorem nonfinite_previous_rejected (w : ℚ) : ¬ previousDivisionSafe false w := by
  simp [previousDivisionSafe]

theorem world_threshold_boundary_rejected :
    ¬ worldDivisionSafe true (1/100000) ∧ ¬ worldDivisionSafe true (-(1/100000)) := by
  norm_num [worldDivisionSafe]

theorem previous_nonpositive_rejected (finite : Bool) (w : ℚ) (h : w ≤ 0) :
    ¬ previousDivisionSafe finite w := by
  unfold previousDivisionSafe
  intro safe
  linarith [safe.2]

theorem guarded_ratio_bound (finite : Bool) (c w : ℚ) (h : worldDivisionSafe finite w) :
    |c/w| ≤ |c|/(1/100000) := by
  rw [abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg c) (by norm_num) (le_of_lt h.2)

--ai: the rational bound can still exceed IEEE range; shader checks normalized results AGAIN.
theorem tiny_denominator_can_amplify : |(1 : ℚ)/(1/100000)| = 100000 := by norm_num

end GxProofsGfx.TemporalSampling
