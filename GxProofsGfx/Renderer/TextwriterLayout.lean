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
  gX — TextWriter Layout Invariants

  Salvaged from gameX lean/GameXProofs/TextwriterLayout.lean,
  re-verified constant by constant against gX source:
    - GX_TEXTWRITER_WRAP_RATIO    = 0.85  (textwriter.h:69)
    - GX_TEXTWRITER_ADVANCE_RATIO = 0.6   (textwriter.h:71)
    - GX_TEXTWRITER_WORD_SPACING  = 3.0   (textwriter.h:72)
    - GX_TEXTWRITER_DEFAULT_SIZE  = 24.0  (textwriter.h:61)
    - RAINBOW_HUE_SPEED  = 0.15, TIME_SPEED = 0.5 (textwriter.h:75-76)

  Wrap width (textwriter.c:841):
    - wrapX = renderWidth · 0.85

  Glyph advance (textwriter.c:962-969):
    - advance = fs · 0.6, clamped back to it when below 1.0
    - measured advance ≥ 1 is retained even when below fs · ADVANCE_RATIO

  Font size (textwriter.c:867):
    - fs = word->size > 1.0 ? word->size : 24.0

  Rainbow effect (textwriter.c:906):
    - hue = fmod(giRel · 0.15 + effectTime · 0.5, 1.0) ∈ [0, 1)

  Theorems proven: 14
    - wrap_ratio_valid:      WRAP_RATIO ∈ (0, 1)
    - advance_ratio_valid:   ADVANCE_RATIO ∈ (0, 1)
    - wrap_x_positive:       wrapX > 0 for renderWidth > 0
    - wrap_x_below_width:    wrapX < renderWidth (wraps before the edge)
    - default_size_valid:    DEFAULT_SIZE ≥ 1.0 (guards the size check)
    - font_size_min:         DEFAULT_SIZE ≥ 24
    - advance_min:           advance ≥ min(1, fs·ADVANCE_RATIO)
    - advance_positive:      advance > 0 for fs > 0
    - word_spacing_positive: WORD_SPACING > 0
    - rainbow_hue_nonneg:    nonnegative phase ⇒ hue ≥ 0
    - rainbow_hue_lt_one:    hue < 1
    - rainbow_hue_in_unit:   nonnegative phase ⇒ fmod result ∈ [0, 1)
    - measured_advance_can_be_below_fallback: counterexample to the old bound
    - negative_hue_has_negative_remainder: counterexample to unsigned wrapping

  Continuous math is modeled over ℝ, not IEEE float rounding. Signed hue
  wrapping models fmod's sign; the [0, 1) claim requires nonnegative phase.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
--ai: the pinned Mathlib exposes floor through its split ring module.
import Mathlib.Algebra.Order.Floor.Ring

namespace GxProofsGfx.TextwriterLayout

-- =============================================================
-- 1. Constants
-- =============================================================

-- Layout constants (textwriter.h).
def WRAP_RATIO : ℝ := 0.85
def ADVANCE_RATIO : ℝ := 0.6
def WORD_SPACING : ℝ := 3.0
def DEFAULT_SIZE : ℝ := 24.0
def RAINBOW_HUE_SPEED : ℝ := 0.15
def RAINBOW_TIME_SPEED : ℝ := 0.5

-- WRAP_RATIO ∈ (0, 1).
theorem wrap_ratio_valid :
    0 < WRAP_RATIO ∧ WRAP_RATIO < 1 := by
  norm_num [WRAP_RATIO]

-- ADVANCE_RATIO ∈ (0, 1).
theorem advance_ratio_valid :
    0 < ADVANCE_RATIO ∧ ADVANCE_RATIO < 1 := by
  norm_num [ADVANCE_RATIO]

-- WORD_SPACING > 0.
theorem word_spacing_positive :
    0 < WORD_SPACING := by
  norm_num [WORD_SPACING]

-- DEFAULT_SIZE ≥ 1.0 (the `word->size > 1.0` check in textwriter.c:867).
theorem default_size_valid :
    1 ≤ DEFAULT_SIZE := by
  norm_num [DEFAULT_SIZE]

-- =============================================================
-- 2. Wrap width
-- =============================================================

-- wrapX = renderWidth · 0.85 (textwriter.c:841).
noncomputable def wrapX (renderWidth : ℝ) : ℝ :=
  renderWidth * WRAP_RATIO

-- wrapX > 0 for renderWidth > 0.
theorem wrap_x_positive (renderWidth : ℝ) (h : 0 < renderWidth) :
    0 < wrapX renderWidth := by
  unfold wrapX
  have hratio : 0 < WRAP_RATIO := (wrap_ratio_valid).1
  exact mul_pos h hratio

-- wrapX < renderWidth: wrapping happens before the right edge.
theorem wrap_x_below_width (renderWidth : ℝ) (h : 0 < renderWidth) :
    wrapX renderWidth < renderWidth := by
  unfold wrapX
  have hratio : WRAP_RATIO < 1 := (wrap_ratio_valid).2
  have hmul : renderWidth * WRAP_RATIO < renderWidth * 1 := by
    exact mul_lt_mul_of_pos_left hratio h
  simpa using hmul

-- =============================================================
-- 3. Font size and advance
-- =============================================================

-- fs = word->size > 1.0 ? word->size : DEFAULT_SIZE (textwriter.c:867).
-- For size ≤ 1.0, fs = DEFAULT_SIZE.
theorem font_size_min :
    DEFAULT_SIZE ≥ 24 := by
  norm_num [DEFAULT_SIZE]

--ai: model the measured glyph branch and its <1 fallback, not just the fallback expression.
noncomputable def glyphAdvance (fs : ℝ) (hasGlyph : Bool) (measured : ℝ) : ℝ :=
  if hasGlyph then
    if measured < 1 then fs * ADVANCE_RATIO else measured
  else fs * ADVANCE_RATIO

theorem advance_min (fs : ℝ) (hasGlyph : Bool) (measured : ℝ) :
    min 1 (fs * ADVANCE_RATIO) ≤ glyphAdvance fs hasGlyph measured := by
  cases hasGlyph
  · simp [glyphAdvance]
  · by_cases h : measured < 1
    · simp [glyphAdvance, h]
    · exact (min_le_left 1 (fs * ADVANCE_RATIO)).trans (by simpa [glyphAdvance, h] using le_of_not_gt h)

theorem advance_positive (fs : ℝ) (hasGlyph : Bool) (measured : ℝ) (h : 0 < fs) :
    0 < glyphAdvance fs hasGlyph measured := by
  have fallback : 0 < fs * ADVANCE_RATIO := mul_pos h (advance_ratio_valid).1
  cases hasGlyph
  · simpa [glyphAdvance] using fallback
  · by_cases hm : measured < 1
    · simpa [glyphAdvance, hm] using fallback
    · simpa [glyphAdvance, hm] using (show (0 : ℝ) < measured by linarith [le_of_not_gt hm])

--ai: a valid one-unit measured glyph disproves the former prose claim about fallback-sized advance.
theorem measured_advance_can_be_below_fallback :
    glyphAdvance 24 true 1 = 1 ∧ glyphAdvance 24 true 1 < 24 * ADVANCE_RATIO := by
  norm_num [glyphAdvance, ADVANCE_RATIO]

-- =============================================================
-- 4. Rainbow hue
-- =============================================================

-- Rainbow hue (textwriter.c:906):
--   hue = fmod(giRel·HUE_SPEED + effectTime·TIME_SPEED, 1.0)
--ai: fmod truncates toward zero; a negative phase has a negative remainder.
noncomputable def signedRemainder (x : ℝ) : ℝ :=
  if x < 0 then -((-x) - (Int.floor (-x) : ℝ))
  else x - (Int.floor x : ℝ)

noncomputable def rainbowHue (giRel effectTime : ℝ) : ℝ :=
  signedRemainder (giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED)

-- The hue (fractional part) is ≥ 0.
theorem rainbow_hue_nonneg (giRel effectTime : ℝ)
    (hphase : 0 ≤ giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED) :
    0 ≤ rainbowHue giRel effectTime := by
  unfold rainbowHue signedRemainder
  rw [if_neg (not_lt_of_ge hphase)]
  have hfl : (Int.floor (giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED) : ℝ) ≤
      giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED :=
    Int.floor_le (giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED)
  linarith

-- The hue (fractional part) is < 1.
theorem rainbow_hue_lt_one (giRel effectTime : ℝ) :
    rainbowHue giRel effectTime < 1 := by
  unfold rainbowHue signedRemainder
  split
  · have hfl := Int.floor_le (-(giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED))
    linarith
  · have hlt := Int.lt_floor_add_one (giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED)
    linarith

-- The hue wraps into [0, 1).
theorem rainbow_hue_in_unit (giRel effectTime : ℝ)
    (hphase : 0 ≤ giRel * RAINBOW_HUE_SPEED + effectTime * RAINBOW_TIME_SPEED) :
    0 ≤ rainbowHue giRel effectTime ∧ rainbowHue giRel effectTime < 1 := by
  constructor
  · exact rainbow_hue_nonneg giRel effectTime hphase
  · exact rainbow_hue_lt_one giRel effectTime

--ai: retain a negative-phase witness so an unsigned fractional-part substitution cannot return unnoticed.
theorem negative_hue_has_negative_remainder : rainbowHue 0 (-1) = -(1 / 2 : ℝ) := by
  norm_num [rainbowHue, signedRemainder, RAINBOW_HUE_SPEED, RAINBOW_TIME_SPEED]

end GxProofsGfx.TextwriterLayout
