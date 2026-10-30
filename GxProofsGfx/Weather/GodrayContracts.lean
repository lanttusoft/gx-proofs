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
  //ai: bounded four-tap stride from resources/shader/gfx_godray_gen.frag.
  Scalar exact contracts require positive distance/density as stated. GLSL LOD
  selection, normalization/rounding, source freshness and GPU sampling are external.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace GxProofsGfx.GodrayContracts

def oldStride (distance density : ℚ) : ℚ := distance*4 / max density 1
def stride (distance density : ℚ) : ℚ := min (oldStride distance density) (distance/4)

theorem denominator_positive (density : ℚ) : 0 < max density 1 := by
  have h := le_max_right density (1 : ℚ)
  linarith

theorem stride_nonnegative (distance density : ℚ) (hd : 0 ≤ distance) :
    0 ≤ stride distance density := by
  unfold stride oldStride
  apply le_min
  · exact div_nonneg (by linarith) (le_of_lt (denominator_positive density))
  · linarith

theorem stride_bounded (distance density : ℚ) : stride distance density ≤ distance/4 :=
  min_le_right _ _

theorem high_density_preserves_stride (distance density : ℚ)
    (hd : 0 ≤ distance) (hn : 16 ≤ density) :
    stride distance density = oldStride distance density := by
  unfold stride
  apply min_eq_left
  unfold oldStride
  rw [max_eq_left (by linarith)]
  apply (div_le_iff₀ (by linarith : 0 < density)).mpr
  nlinarith

theorem low_density_full_span (distance density : ℚ)
    (hd : 0 ≤ distance) (hn : density ≤ 16) : stride distance density = distance/4 := by
  unfold stride
  apply min_eq_right
  unfold oldStride
  have hm : max density 1 ≤ (16 : ℚ) := max_le hn (by norm_num)
  apply (le_div_iff₀ (denominator_positive density)).mpr
  nlinarith

theorem four_taps_do_not_overshoot (distance density index : ℚ)
    (hd : 0 ≤ distance) (hi : 0 ≤ index) (hu : index ≤ 4) :
    0 ≤ index*stride distance density ∧ index*stride distance density ≤ distance := by
  have hs := stride_nonnegative distance density hd
  have hb := stride_bounded distance density
  constructor
  · exact mul_nonneg hi hs
  · nlinarith

def tapFraction (distance density index : ℚ) : ℚ := index*stride distance density/distance

theorem tap_fraction_range (distance density index : ℚ)
    (hd : 0 < distance) (hi : 0 ≤ index) (hu : index ≤ 4) :
    0 ≤ tapFraction distance density index ∧ tapFraction distance density index ≤ 1 := by
  have ht := four_taps_do_not_overshoot distance density index (le_of_lt hd) hi hu
  unfold tapFraction
  constructor
  · exact div_nonneg ht.1 (le_of_lt hd)
  · exact (div_le_one hd).mpr ht.2

theorem tap_stays_between_pixel_and_sun (pixel sun fraction : ℚ)
    (hp : pixel ≤ sun) (hl : 0 ≤ fraction) (hu : fraction ≤ 1) :
    pixel ≤ pixel+(sun-pixel)*fraction ∧ pixel+(sun-pixel)*fraction ≤ sun := by
  constructor <;> nlinarith

theorem reversed_axis_tap_stays_between (pixel sun fraction : ℚ)
    (hp : sun ≤ pixel) (hl : 0 ≤ fraction) (hu : fraction ≤ 1) :
    sun ≤ pixel+(sun-pixel)*fraction ∧ pixel+(sun-pixel)*fraction ≤ pixel := by
  constructor <;> nlinarith

theorem old_density_one_overshoot : 1 < 4*oldStride 1 1 := by norm_num [oldStride]
theorem old_density_fifteen_overshoot : 1 < 4*oldStride 1 15 := by norm_num [oldStride]

end GxProofsGfx.GodrayContracts
