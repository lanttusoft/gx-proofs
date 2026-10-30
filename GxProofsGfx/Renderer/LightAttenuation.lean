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
  //ai: exact-real point-light attenuation and clustered-radius contracts.

  The shader model is 1 / (k0 + k1*d + k2*d^2). Under nonnegative
  coefficients and distance, its denominator is nondecreasing; when k0 is
  positive, the reciprocal attenuation is nonincreasing. The clustered radius
  solves the brightness-weighted epsilon boundary for positive quadratic and
  linear-only coefficients. A constant light above epsilon has no finite
  cutoff and is assigned to every tile. The exact-real policy sends negative
  decay coefficients to its unbounded case. The C implementation also maps
  non-finite inputs to all tiles; that machine-value guard is not modeled over
  the reals. These are exact-real algebraic claims, not IEEE or GPU guarantees.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.Renderer.LightAttenuation

def attenuationDenominator (k0 k1 k2 distance : ℝ) : ℝ :=
  k0 + k1 * distance + k2 * distance ^ 2

noncomputable def pointAttenuation (k0 k1 k2 distance : ℝ) : ℝ :=
  1 / attenuationDenominator k0 k1 k2 distance

theorem denominator_nonnegative (k0 k1 k2 distance : ℝ)
    (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (hdistance : 0 ≤ distance) :
    0 ≤ attenuationDenominator k0 k1 k2 distance := by
  unfold attenuationDenominator
  positivity

theorem denominator_positive (k0 k1 k2 distance : ℝ)
    (hk0 : 0 < k0) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (hdistance : 0 ≤ distance) :
    0 < attenuationDenominator k0 k1 k2 distance := by
  have hrest : 0 ≤ k1 * distance + k2 * distance ^ 2 := by positivity
  unfold attenuationDenominator
  linarith

theorem denominator_monotone (k0 k1 k2 nearDistance farDistance : ℝ)
    (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (hnear : 0 ≤ nearDistance) (horder : nearDistance ≤ farDistance) :
    attenuationDenominator k0 k1 k2 nearDistance ≤
      attenuationDenominator k0 k1 k2 farDistance := by
  have hlinear : k1 * nearDistance ≤ k1 * farDistance :=
    mul_le_mul_of_nonneg_left horder hk1
  have hsquare : nearDistance ^ 2 ≤ farDistance ^ 2 := by
    nlinarith
  have hquadratic : k2 * nearDistance ^ 2 ≤ k2 * farDistance ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hk2
  unfold attenuationDenominator
  linarith

theorem attenuation_nonincreasing (k0 k1 k2 nearDistance farDistance : ℝ)
    (hk0 : 0 < k0) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (hnear : 0 ≤ nearDistance) (horder : nearDistance ≤ farDistance) :
    pointAttenuation k0 k1 k2 farDistance ≤
      pointAttenuation k0 k1 k2 nearDistance := by
  have hnearDen := denominator_positive k0 k1 k2 nearDistance hk0 hk1 hk2 hnear
  have hdenOrder := denominator_monotone k0 k1 k2 nearDistance farDistance
    hk1 hk2 hnear horder
  unfold pointAttenuation
  exact one_div_le_one_div_of_le hnearDen hdenOrder

theorem attenuation_nonincreasing_from_positive_near
    (k0 k1 k2 nearDistance farDistance : ℝ)
    (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (hnear : 0 ≤ nearDistance) (horder : nearDistance ≤ farDistance)
    (hnearDen : 0 < attenuationDenominator k0 k1 k2 nearDistance) :
    pointAttenuation k0 k1 k2 farDistance ≤
      pointAttenuation k0 k1 k2 nearDistance := by
  have hdenOrder := denominator_monotone k0 k1 k2 nearDistance farDistance
    hk1 hk2 hnear horder
  unfold pointAttenuation
  exact one_div_le_one_div_of_le hnearDen hdenOrder

noncomputable def clusterEpsilon : ℝ := 1 / 250

theorem clusterEpsilon_positive : 0 < clusterEpsilon := by
  norm_num [clusterEpsilon]

noncomputable def clusterTarget (brightness k0 : ℝ) : ℝ :=
  brightness / clusterEpsilon - k0

noncomputable def quadraticRadiusFormula (k1 kq target : ℝ) : ℝ :=
  (-k1 + Real.sqrt (k1 ^ 2 + 4 * kq * target)) / (2 * kq)

noncomputable def quadraticRadius (k1 kq target : ℝ) : ℝ :=
  let root := quadraticRadiusFormula k1 kq target
  if root < 0 then 0 else root

inductive ClusterRadius where
  | zero
  | finite (distance : ℝ)
  | unbounded

noncomputable def clusterRadiusPolicy
    (brightness k0 k1 k2 : ℝ) : ClusterRadius :=
  let target := clusterTarget brightness k0
  if k1 < 0 ∨ k2 < 0 then .unbounded
  else if target ≤ 0 then .zero
  else if k2 = 0 then
    if 0 < k1 then .finite (target / k1) else .unbounded
  else .finite (quadraticRadius k1 k2 target)

noncomputable def clusterEffectiveRadius
    (brightness k0 k1 k2 : ℝ) : ℝ :=
  let target := clusterTarget brightness k0
  if target ≤ 0 then 0
  else quadraticRadius k1 k2 target

theorem quadraticRadiusFormula_nonnegative (k1 kq target : ℝ)
    (hk1 : 0 ≤ k1) (hkq : 0 < kq) (htarget : 0 < target) :
    0 ≤ quadraticRadiusFormula k1 kq target := by
  let discriminant := k1 ^ 2 + 4 * kq * target
  have hdisc : 0 ≤ discriminant := by
    dsimp [discriminant]
    positivity
  have hsquare : Real.sqrt discriminant ^ 2 = discriminant :=
    Real.sq_sqrt hdisc
  have hroot : k1 ≤ Real.sqrt discriminant := by
    by_contra hnot
    have hlt : Real.sqrt discriminant < k1 := lt_of_not_ge hnot
    have hproduct :
        0 < (k1 - Real.sqrt discriminant) * (k1 + Real.sqrt discriminant) :=
      mul_pos (by linarith) (by positivity)
    dsimp [discriminant] at hsquare
    nlinarith [mul_pos hkq htarget, hproduct]
  unfold quadraticRadiusFormula
  apply div_nonneg
  · linarith
  · positivity

theorem quadraticRadius_nonnegative (k1 kq target : ℝ) :
    0 ≤ quadraticRadius k1 kq target := by
  unfold quadraticRadius
  dsimp
  split_ifs with h
  · norm_num
  · exact le_of_not_gt h

theorem quadraticRadius_solves_cutoff (k1 kq target : ℝ)
    (hk1 : 0 ≤ k1) (hkq : 0 < kq) (htarget : 0 < target) :
    k1 * quadraticRadius k1 kq target +
      kq * quadraticRadius k1 kq target ^ 2 = target := by
  have hrootNonnegative := quadraticRadiusFormula_nonnegative k1 kq target
    hk1 hkq htarget
  have hclamp : quadraticRadius k1 kq target =
      quadraticRadiusFormula k1 kq target := by
    unfold quadraticRadius
    dsimp
    split_ifs with h
    · exact False.elim ((not_lt_of_ge hrootNonnegative) h)
    · rfl
  rw [hclamp]
  unfold quadraticRadiusFormula
  have hdisc : 0 ≤ k1 ^ 2 + 4 * kq * target := by positivity
  have hsquare := Real.sq_sqrt hdisc
  have hden : 2 * kq ≠ 0 := ne_of_gt (by positivity)
  field_simp [hden]
  nlinarith [hsquare]

theorem cluster_radius_solves_shader_cutoff
    (brightness k0 k1 k2 : ℝ)
    (hk1 : 0 ≤ k1) (hk2 : 0 < k2)
    (htarget : 0 < clusterTarget brightness k0) :
    attenuationDenominator k0 k1 k2
        (clusterEffectiveRadius brightness k0 k1 k2) =
      brightness / clusterEpsilon := by
  have hroot := quadraticRadius_solves_cutoff k1
    k2 (clusterTarget brightness k0) hk1 hk2 htarget
  have hradius : clusterEffectiveRadius brightness k0 k1 k2 =
      quadraticRadius k1 k2 (clusterTarget brightness k0) := by
    simp [clusterEffectiveRadius, not_le_of_gt htarget]
  rw [hradius] at *
  unfold attenuationDenominator clusterTarget at *
  nlinarith [hroot]

theorem cluster_radius_reaches_epsilon
    (brightness k0 k1 k2 : ℝ)
    (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) (hk2 : 0 < k2)
    (htarget : 0 < clusterTarget brightness k0) :
    brightness * pointAttenuation k0 k1 k2
        (clusterEffectiveRadius brightness k0 k1 k2) = clusterEpsilon := by
  have hden := cluster_radius_solves_shader_cutoff brightness k0 k1 k2
    hk1 hk2 htarget
  have hratio : 0 < brightness / clusterEpsilon := by
    unfold clusterTarget at htarget
    linarith [hk0]
  have hbrightnessPositive : 0 < brightness := by
    have hcancel :
        (brightness / clusterEpsilon) * clusterEpsilon = brightness := by
      field_simp [ne_of_gt clusterEpsilon_positive]
    rw [← hcancel]
    exact mul_pos hratio clusterEpsilon_positive
  unfold pointAttenuation
  rw [hden]
  field_simp [ne_of_gt hbrightnessPositive, ne_of_gt clusterEpsilon_positive]

theorem cluster_beyond_radius_is_at_most_epsilon
    (brightness k0 k1 k2 distance : ℝ)
    (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) (hk2 : 0 < k2)
    (htarget : 0 < clusterTarget brightness k0)
    (hfar : clusterEffectiveRadius brightness k0 k1 k2 ≤ distance) :
    brightness * pointAttenuation k0 k1 k2 distance ≤ clusterEpsilon := by
  have hradiusEq : clusterEffectiveRadius brightness k0 k1 k2 =
      quadraticRadius k1 k2 (clusterTarget brightness k0) := by
    simp [clusterEffectiveRadius, not_le_of_gt htarget]
  have hradiusNonnegative :
      0 ≤ clusterEffectiveRadius brightness k0 k1 k2 := by
    rw [hradiusEq]
    exact quadraticRadius_nonnegative k1 k2 (clusterTarget brightness k0)
  have hdenAtRadius := cluster_radius_solves_shader_cutoff brightness k0 k1 k2
    hk1 hk2 htarget
  have hratioPositive : 0 < brightness / clusterEpsilon := by
    unfold clusterTarget at htarget
    linarith [hk0]
  have hdenPositive :
      0 < attenuationDenominator k0 k1 k2
        (clusterEffectiveRadius brightness k0 k1 k2) := by
    rw [hdenAtRadius]
    exact hratioPositive
  have hfalloff := attenuation_nonincreasing_from_positive_near
    k0 k1 k2 (clusterEffectiveRadius brightness k0 k1 k2) distance
    hk1 (le_of_lt hk2) hradiusNonnegative hfar hdenPositive
  have hbrightnessPositive : 0 < brightness := by
    have hcancel :
        (brightness / clusterEpsilon) * clusterEpsilon = brightness := by
      field_simp [ne_of_gt clusterEpsilon_positive]
    rw [← hcancel]
    exact mul_pos hratioPositive clusterEpsilon_positive
  have hweighted := mul_le_mul_of_nonneg_left hfalloff
    (le_of_lt hbrightnessPositive)
  calc
    brightness * pointAttenuation k0 k1 k2 distance ≤
        brightness * pointAttenuation k0 k1 k2
          (clusterEffectiveRadius brightness k0 k1 k2) := hweighted
    _ = clusterEpsilon := cluster_radius_reaches_epsilon brightness k0 k1 k2
      hk0 hk1 hk2 htarget

theorem cluster_zero_radius_brightness_below_epsilon
    (brightness k0 : ℝ)
    (htarget : clusterTarget brightness k0 ≤ 0) :
    brightness ≤ clusterEpsilon * k0 := by
  have hratio : brightness / clusterEpsilon ≤ k0 := by
    unfold clusterTarget at htarget
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hratio
    (le_of_lt clusterEpsilon_positive)
  have hcancel :
      (brightness / clusterEpsilon) * clusterEpsilon = brightness := by
    field_simp [ne_of_gt clusterEpsilon_positive]
  rw [hcancel] at hscaled
  simpa [mul_comm] using hscaled

theorem linearRadius_solves_cutoff (linear target : ℝ) (hlinear : 0 < linear) :
    linear * (target / linear) = target := by
  field_simp [ne_of_gt hlinear]

theorem positive_linear_policy_uses_finite_radius
    (brightness k0 k1 : ℝ) (hlinear : 0 < k1)
    (htarget : 0 < clusterTarget brightness k0) :
    clusterRadiusPolicy brightness k0 k1 0 =
      .finite (clusterTarget brightness k0 / k1) := by
  simp [clusterRadiusPolicy, not_le_of_gt htarget,
    not_lt.mpr (le_of_lt hlinear), hlinear]

theorem cluster_linear_radius_solves_shader_cutoff
    (brightness k0 k1 : ℝ) (hlinear : 0 < k1) :
    attenuationDenominator k0 k1 0 (clusterTarget brightness k0 / k1) =
      brightness / clusterEpsilon := by
  have hroot := linearRadius_solves_cutoff k1
    (clusterTarget brightness k0) hlinear
  unfold attenuationDenominator clusterTarget at *
  nlinarith [hroot]

theorem cluster_linear_radius_reaches_epsilon
    (brightness k0 k1 : ℝ) (hk0 : 0 ≤ k0) (hlinear : 0 < k1)
    (htarget : 0 < clusterTarget brightness k0) :
    brightness * pointAttenuation k0 k1 0
        (clusterTarget brightness k0 / k1) = clusterEpsilon := by
  have hden := cluster_linear_radius_solves_shader_cutoff
    brightness k0 k1 hlinear
  have hratio : 0 < brightness / clusterEpsilon := by
    unfold clusterTarget at htarget
    linarith [hk0]
  have hbrightnessPositive : 0 < brightness := by
    have hcancel :
        (brightness / clusterEpsilon) * clusterEpsilon = brightness := by
      field_simp [ne_of_gt clusterEpsilon_positive]
    rw [← hcancel]
    exact mul_pos hratio clusterEpsilon_positive
  unfold pointAttenuation
  rw [hden]
  field_simp [ne_of_gt hbrightnessPositive, ne_of_gt clusterEpsilon_positive]

theorem constant_attenuation_is_distance_independent
    (brightness k0 nearDistance farDistance : ℝ) :
    brightness * pointAttenuation k0 0 0 nearDistance =
      brightness * pointAttenuation k0 0 0 farDistance := by
  simp [pointAttenuation, attenuationDenominator]

theorem constant_above_threshold_has_no_finite_radius
    (brightness k0 : ℝ) (htarget : 0 < clusterTarget brightness k0) :
    clusterRadiusPolicy brightness k0 0 0 = .unbounded := by
  simp [clusterRadiusPolicy, not_le_of_gt htarget]

theorem constant_below_threshold_uses_zero_radius
    (brightness k0 : ℝ) (htarget : clusterTarget brightness k0 ≤ 0) :
    clusterRadiusPolicy brightness k0 0 0 = .zero := by
  simp [clusterRadiusPolicy, htarget]

theorem negative_coefficients_use_unbounded_radius
    (brightness k0 k1 k2 : ℝ) (hnegative : k1 < 0 ∨ k2 < 0) :
    clusterRadiusPolicy brightness k0 k1 k2 = .unbounded := by
  simp [clusterRadiusPolicy, hnegative]

theorem positive_quadratic_policy_uses_shader_coefficients
    (brightness k0 k1 k2 : ℝ) (hk1 : 0 ≤ k1) (hk2 : 0 < k2)
    (htarget : 0 < clusterTarget brightness k0) :
    clusterRadiusPolicy brightness k0 k1 k2 =
      .finite (quadraticRadius k1 k2 (clusterTarget brightness k0)) := by
  simp [clusterRadiusPolicy, not_le_of_gt htarget,
    not_lt.mpr hk1, not_lt.mpr (le_of_lt hk2), ne_of_gt hk2]

end GxProofsGfx.Renderer.LightAttenuation
