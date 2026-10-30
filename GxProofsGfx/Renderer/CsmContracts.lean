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
  //ai: source-grounded cascade selection and conditional projection/blending.
  Dynamic splits, view-depth versus ray-distance, GPU accuracy remain explicit.
-/
import GxProofsGfx.Renderer.PointShadowDepth

namespace GxProofsGfx.CsmContracts

def select (count : ℕ) (s0 s1 s2 distance : ℚ) : ℕ :=
  if count > 1 ∧ s0 > 0 then
    if distance > s2 ∧ count ≥ 4 then 3
    else if distance > s1 ∧ count ≥ 3 then 2
    else if distance > s0 then 1 else 0
  else 0

theorem layer_in_range (count : ℕ) (s0 s1 s2 distance : ℚ)
    (hn : 1 ≤ count) : select count s0 s1 s2 distance < count := by
  unfold select
  split_ifs <;> omega

theorem layer_at_most_three (count : ℕ) (s0 s1 s2 distance : ℚ) :
    select count s0 s1 s2 distance ≤ 3 := by
  unfold select
  split_ifs <;> omega

theorem disabled_first_split (count : ℕ) (s0 s1 s2 distance : ℚ) (h : s0 ≤ 0) :
    select count s0 s1 s2 distance = 0 := by
  simp [select,not_lt_of_ge h]

theorem exact_first_boundary (s0 s1 s2 : ℚ) (h0 : 0 < s0) (h1 : s0 < s1) (h2 : s1 < s2) :
    select 4 s0 s1 s2 s0 = 0 := by
  have h02 : ¬ s2 < s0 := by linarith
  simp [select,h0,not_lt_of_ge (le_of_lt h1),h02]

theorem exact_second_boundary (s0 s1 s2 : ℚ) (h0 : 0 < s0) (h1 : s0 < s1) (h2 : s1 < s2) :
    select 4 s0 s1 s2 s1 = 1 := by
  simp [select,h0,h1,not_lt_of_ge (le_of_lt h2)]

theorem exact_third_boundary (s0 s1 s2 : ℚ) (h0 : 0 < s0) (h1 : s0 < s1) (h2 : s1 < s2) :
    select 4 s0 s1 s2 s2 = 2 := by
  simp [select,h0,h2]

--ai: equal/unsorted splits cannot use the strict ordered-boundary conclusions.
theorem equal_splits_jump : select 4 10 10 10 11 = 3 := by
  norm_num [select]

def smooth (u : ℚ) : ℚ := u*u*(3-2*u)
def mix (previous current weight : ℚ) : ℚ := (1-weight)*previous+weight*current

theorem smooth_endpoints : smooth 0 = 0 ∧ smooth 1 = 1 := by
  norm_num [smooth]

theorem smooth_bounds (u : ℚ) (hl : 0 ≤ u) (hu : u ≤ 1) : 0 ≤ smooth u ∧ smooth u ≤ 1 := by
  have h1 : 0 ≤ u*u*(3-2*u) := mul_nonneg (mul_nonneg hl hl) (by linarith)
  have h2 : 0 ≤ (1-u)^2*(1+2*u) := mul_nonneg (sq_nonneg _) (by linarith)
  unfold smooth
  constructor
  · exact h1
  · nlinarith

theorem mix_endpoints (previous current : ℚ) : mix previous current (smooth 0) = previous ∧
    mix previous current (smooth 1) = current := by
  norm_num [mix,smooth]

theorem mix_bounds (previous current weight : ℚ)
    (hp : 0 ≤ previous ∧ previous ≤ 1) (hc : 0 ≤ current ∧ current ≤ 1)
    (hw : 0 ≤ weight ∧ weight ≤ 1) : 0 ≤ mix previous current weight ∧ mix previous current weight ≤ 1 := by
  have p := mul_nonneg (by linarith : 0 ≤ 1-weight) hp.1
  have c := mul_nonneg hw.1 hc.1
  have pu := mul_le_mul_of_nonneg_left hp.2 (by linarith : 0 ≤ 1-weight)
  have cu := mul_le_mul_of_nonneg_left hc.2 hw.1
  unfold mix
  constructor <;> nlinarith

def width (boundary scale : ℚ) : ℚ := boundary*(1+scale/10)-boundary
theorem positive_blend_width (boundary scale : ℚ) (hb : 0 < boundary) (hs : 0 < scale) :
    0 < width boundary scale := by
  unfold width
  nlinarith [mul_pos hb hs]

--ai: new-cascade fade starts at previous sample; it matches preceding output only if preceding fade finished.
theorem overlapping_fade_counterexample :
    mix 0 1 (smooth (1/2)) ≠ mix 1 0 (smooth 0) := by
  norm_num [mix,smooth]

theorem boundary_agreement_if_previous_fade_finished (earlier previous current weight : ℚ)
    (h : weight = 1) : mix earlier previous weight = mix previous current (smooth 0) := by
  simp [h,mix,smooth]

theorem nonoverlap_normalized_coordinate (boundary next scale : ℚ)
    (hb : 0 < boundary) (hs : 0 < scale)
    (hgap : boundary*(1+scale/10) ≤ next) :
    1 ≤ (next-boundary)/width boundary scale := by
  have hw := positive_blend_width boundary scale hb hs
  rw [le_div_iff₀ hw]
  unfold width
  linarith

def projected (coordinate w : ℚ) : ℚ := (coordinate/w+1)/2
theorem positive_w_bounds (coordinate w : ℚ) (hw : 0 < w) :
    (0 ≤ projected coordinate w ∧ projected coordinate w ≤ 1) ↔ (-w ≤ coordinate ∧ coordinate ≤ w) := by
  unfold projected
  constructor
  · intro h
    constructor
    · have : -1 ≤ coordinate/w := by linarith [h.1]
      have := (le_div_iff₀ hw).mp this
      linarith
    · have : coordinate/w ≤ 1 := by linarith [h.2]
      have := (div_le_iff₀ hw).mp this
      linarith
  · intro h
    have hl : -1 ≤ coordinate/w := (le_div_iff₀ hw).mpr (by linarith [h.1])
    have hu : coordinate/w ≤ 1 := (div_le_iff₀ hw).mpr (by linarith [h.2])
    constructor <;> linarith

--ai: normalized-depth error differs from radial point-shadow error: no far scaling here.
theorem normalized_compare_error (receiver measured sample stored bias er es : ℚ)
    (hr : |measured-receiver| ≤ er) (hs : |stored-sample| ≤ es) :
    |(measured-bias-stored)-(receiver-bias-sample)| ≤ er+es := by
  have r := abs_le.mp hr
  have s := abs_le.mp hs
  apply abs_le.mpr
  constructor <;> linarith

end GxProofsGfx.CsmContracts
