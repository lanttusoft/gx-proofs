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
  //ai: exact rational weather contracts grounded in src/renderer/gfx/weather.c.
  remainder is supplied by an external fmodf obligation; random picks must lie in
  [0,1]. These handwritten models do not certify IEEE arithmetic, remainder
  computation, camera chronology, random generators, particle motion or GPU draws.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace GxProofsGfx.WeatherContracts

def corrected (remainder width : ℚ) : ℚ :=
  if remainder < 0 then remainder + width else remainder

theorem corrected_remainder_range (r w : ℚ)
    (hl : -w < r) (hu : r < w) :
    0 ≤ corrected r w ∧ corrected r w < w := by
  unfold corrected
  split_ifs <;> constructor <;> linarith

theorem corrected_remainder_congruence (r w input : ℚ) (quotient : ℤ)
    (hr : r = input-(quotient : ℚ)*w) :
    ∃ q : ℤ, corrected r w = input-(q : ℚ)*w := by
  unfold corrected
  split_ifs
  · use quotient-1
    simp only [Int.cast_sub, Int.cast_one]
    rw [hr]
    ring
  · exact ⟨quotient, hr⟩

def wrap (position center half remainder : ℚ) : ℚ :=
  if half ≤ 0 then center
  else if |position - center| ≤ half then position
  else center + corrected remainder (2 * half) - half

theorem degenerate_wrap_returns_center (p c h r : ℚ) (hh : h ≤ 0) :
    wrap p c h r = c := by simp [wrap, hh]

theorem wrap_preserves_in_bounds (p c h r : ℚ) (hh : 0 < h)
    (hp : |p-c| ≤ h) : wrap p c h r = p := by
  simp [wrap, not_le.mpr hh, hp]

theorem wrap_contains_position (p c h r : ℚ) (hh : 0 < h)
    (hl : -(2*h) < r) (hu : r < 2*h) :
    c-h ≤ wrap p c h r ∧ wrap p c h r ≤ c+h := by
  have hr := corrected_remainder_range r (2*h) hl hu
  unfold wrap
  rw [if_neg (not_le.mpr hh)]
  split_ifs with hp
  · have hb := abs_le.mp hp
    constructor <;> linarith [hb.1, hb.2]
  · constructor <;> linarith [hr.1, hr.2]

theorem wrap_congruence (p c h r : ℚ) (quotient : ℤ) (hh : 0 < h)
    (hr : r = p-c+h-(quotient : ℚ)*(2*h)) :
    ∃ q : ℤ, wrap p c h r = p-(q : ℚ)*(2*h) := by
  unfold wrap
  rw [if_neg (not_le.mpr hh)]
  split_ifs
  · exact ⟨0, by simp⟩
  · obtain ⟨q, hq⟩ := corrected_remainder_congruence r (2*h) (p-c+h) quotient hr
    exact ⟨q, by rw [hq]; ring⟩

--ai: equal supplied remainders are required; floating fmodf translation is not asserted.
theorem wrap_translation (p c h r delta : ℚ) :
    wrap (p+delta) (c+delta) h r = wrap p c h r + delta := by
  have hc : p+delta-(c+delta) = p-c := by ring
  simp only [wrap, hc]
  split_ifs <;> ring

theorem remainder_input_translation (p c h delta : ℚ) :
    (p+delta)-(c+delta)+h = p-c+h := by ring

theorem old_one_width_wrap_counterexample : ¬ (-3 ≤ (0 : ℚ) + 6 - 100) := by
  norm_num

def height (floor ceiling : ℚ) : ℚ :=
  if ceiling-floor ≤ 0 then 1 else ceiling-floor

def bottom (floor ceiling eye : ℚ) : ℚ := max floor (eye-height floor ceiling/2)
def top (floor ceiling eye : ℚ) : ℚ := max (floor+height floor ceiling) (eye+height floor ceiling/2)

theorem height_positive (f t : ℚ) : 0 < height f t := by
  unfold height
  split_ifs <;> linarith

theorem height_preserves_positive_authored_span (f t : ℚ) (h : f < t) :
    height f t = t-f := by simp [height, show ¬ t-f ≤ 0 by linarith]

theorem height_fallback (f t : ℚ) (h : t ≤ f) : height f t = 1 := by
  simp [height, show t-f ≤ 0 by linarith]

theorem band_keeps_world_floor (f t eye : ℚ) : f ≤ bottom f t eye := by
  exact le_max_left _ _

theorem band_keeps_authored_ceiling (f t eye : ℚ) : t ≤ top f t eye := by
  have ht : t ≤ f+height f t := by
    unfold height
    split_ifs <;> linarith
  exact le_trans ht (le_max_left _ _)

theorem band_span (f t eye : ℚ) : top f t eye - bottom f t eye = height f t := by
  unfold top bottom
  rcases le_total f (eye-height f t/2) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith)]
    ring

theorem band_nonempty (f t eye : ℚ) : bottom f t eye < top f t eye := by
  have hh := height_positive f t
  have hs := band_span f t eye
  linarith

theorem band_ground_regime (f t eye : ℚ) (h : eye ≤ f+height f t/2) :
    bottom f t eye = f ∧ top f t eye = f+height f t := by
  unfold bottom top
  constructor <;> apply max_eq_left <;> linarith

theorem band_follows_high_eye (f t eye : ℚ) (h : f+height f t/2 ≤ eye) :
    bottom f t eye = eye-height f t/2 ∧ top f t eye = eye+height f t/2 := by
  unfold bottom top
  constructor <;> apply max_eq_right <;> linarith

def initialSpawn (low high pick : ℚ) : ℚ := low+pick*(high-low)

theorem initial_spawn_range (low high pick : ℚ) (hb : low ≤ high)
    (hl : 0 ≤ pick) (hu : pick ≤ 1) :
    low ≤ initialSpawn low high pick ∧ initialSpawn low high pick ≤ high := by
  unfold initialSpawn
  constructor <;> nlinarith

theorem initial_spawn_above_world_floor (f t eye pick : ℚ)
    (hl : 0 ≤ pick) (hu : pick ≤ 1) :
    f ≤ initialSpawn (bottom f t eye) (top f t eye) pick := by
  have hb := band_keeps_world_floor f t eye
  have hr := initial_spawn_range (bottom f t eye) (top f t eye) pick
    (le_of_lt (band_nonempty f t eye)) hl hu
  exact le_trans hb hr.1

theorem collision_respawn_range (ceiling pick : ℚ) (hl : 0 ≤ pick) (hu : pick ≤ 1) :
    ceiling ≤ ceiling+pick ∧ ceiling+pick ≤ ceiling+1 := by constructor <;> linarith

theorem horizontal_spawn_range (center half pick : ℚ) (hh : 0 ≤ half)
    (hl : 0 ≤ pick) (hu : pick ≤ 1) :
    center-half ≤ center+(2*pick-1)*half ∧ center+(2*pick-1)*half ≤ center+half := by
  constructor <;> nlinarith

def fogHeight (eye pick : ℚ) : ℚ := eye-9/5+pick*(14/5)

theorem fog_height_range (eye pick : ℚ) (hl : 0 ≤ pick) (hu : pick ≤ 1) :
    eye-9/5 ≤ fogHeight eye pick ∧ fogHeight eye pick ≤ eye+1 := by
  unfold fogHeight
  constructor <;> linarith

theorem fog_height_follows_eye (eye pick delta : ℚ) :
    fogHeight (eye+delta) pick = fogHeight eye pick+delta := by
  unfold fogHeight
  ring

def fogFade (worldHeight eye : ℚ) : ℚ := 3/2-(worldHeight-eye+2)/3

theorem fog_fade_translation_invariant (y eye delta : ℚ) :
    fogFade (y+delta) (eye+delta) = fogFade y eye := by
  unfold fogFade
  ring

def boundedFogFade (worldHeight eye : ℚ) : ℚ := max (3/10) (min 1 (fogFade worldHeight eye))

theorem fog_fade_bounds (y eye : ℚ) :
    3/10 ≤ boundedFogFade y eye ∧ boundedFogFade y eye ≤ 1 := by
  unfold boundedFogFade
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem bounded_fog_fade_translation (y eye delta : ℚ) :
    boundedFogFade (y+delta) (eye+delta) = boundedFogFade y eye := by
  simp only [boundedFogFade, fog_fade_translation_invariant]

end GxProofsGfx.WeatherContracts
