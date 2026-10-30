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
  //ai: radial point-shadow encoding/comparison and conditional error margins.
  Radius is supplied: sqrt, GPU depth writes, filtering and coverage external.
-/
import GxProofsGfx.Renderer.CubemapGeometry

namespace GxProofsGfx.PointShadowDepth

def encode (radius far : ℚ) : ℚ := radius / far
def blocked (receiver bias sample far : ℚ) : Prop := receiver-bias > sample*far

theorem radial_roundtrip (radius far : ℚ) (hf : far ≠ 0) : encode radius far * far = radius := by
  unfold encode
  field_simp

theorem encoded_range (radius far : ℚ) (hf : 0 < far) (hr : 0 ≤ radius) (hmax : radius ≤ far) :
    0 ≤ encode radius far ∧ encode radius far ≤ 1 := by
  unfold encode
  exact ⟨div_nonneg hr (le_of_lt hf),(div_le_one hf).mpr hmax⟩

theorem matched_capture_compare (receiver caster bias far : ℚ) (hf : far ≠ 0) :
    blocked receiver bias (encode caster far) far ↔ caster+bias < receiver := by
  unfold blocked
  rw [radial_roundtrip caster far hf]
  constructor <;> intro h <;> linarith

theorem equality_is_lit (receiver bias far : ℚ) (hf : far ≠ 0) :
    ¬ blocked receiver bias (encode (receiver-bias) far) far := by
  rw [matched_capture_compare receiver (receiver-bias) bias far hf]
  simp

theorem bias_monotone (receiver sample far small large : ℚ) (hb : small ≤ large) :
    blocked receiver large sample far → blocked receiver small sample far := by
  unfold blocked
  intro h
  linarith

--ai: clear depth one is lit only when the biased receiver is at most far.
theorem clear_depth_lit (receiver bias far : ℚ) (h : receiver-bias ≤ far) :
    ¬ blocked receiver bias 1 far := by
  unfold blocked
  simpa using not_lt_of_ge h

theorem beyond_far_clear_can_shadow : blocked 11 0 1 10 := by
  norm_num [blocked]

--ai: sampled-depth and receiver errors are supplied, not inferred from depth format.
theorem comparison_error_bound (receiver measured bias caster sample far er es : ℚ)
    (hf : 0 < far) (hr : |measured-receiver| ≤ er)
    (hs : |sample-encode caster far| ≤ es) :
    |(measured-bias-sample*far)-(receiver-bias-caster)| ≤ er+far*es := by
  have r := abs_le.mp hr
  have s := abs_le.mp hs
  have hd := radial_roundtrip caster far (ne_of_gt hf)
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right s.1 (le_of_lt hf),mul_le_mul_of_nonneg_right s.2 (le_of_lt hf)]

theorem robust_shadow (ideal measured error : ℚ) (he : |measured-ideal| ≤ error)
    (hmargin : error < ideal) : 0 < measured := by
  have h := abs_le.mp he
  linarith

theorem robust_lit (ideal measured error : ℚ) (he : |measured-ideal| ≤ error)
    (hmargin : ideal ≤ -error) : measured ≤ 0 := by
  have h := abs_le.mp he
  linarith

def tap (receiver bias sample far : ℚ) : ℚ := if receiver-bias > sample*far then 1 else 0
theorem tap_range (receiver bias sample far : ℚ) :
    0 ≤ tap receiver bias sample far ∧ tap receiver bias sample far ≤ 1 := by
  unfold tap
  split <;> norm_num

def pcf5 (a b c d e : ℚ) : ℚ := (a+b+c+d+e)/5
theorem five_tap_bounds (a b c d e : ℚ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hd : 0 ≤ d ∧ d ≤ 1) (he : 0 ≤ e ∧ e ≤ 1) :
    0 ≤ pcf5 a b c d e ∧ pcf5 a b c d e ≤ 1 := by
  unfold pcf5
  constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hd.1,hd.2,he.1,he.2]

theorem production_tap_average_bounds (receiver bias far a b c d e : ℚ) :
    0 ≤ pcf5 (tap receiver bias a far) (tap receiver bias b far)
      (tap receiver bias c far) (tap receiver bias d far) (tap receiver bias e far) ∧
    pcf5 (tap receiver bias a far) (tap receiver bias b far)
      (tap receiver bias c far) (tap receiver bias d far) (tap receiver bias e far) ≤ 1 := by
  exact five_tap_bounds _ _ _ _ _ (tap_range _ _ _ _) (tap_range _ _ _ _)
    (tap_range _ _ _ _) (tap_range _ _ _ _) (tap_range _ _ _ _)

end GxProofsGfx.PointShadowDepth
