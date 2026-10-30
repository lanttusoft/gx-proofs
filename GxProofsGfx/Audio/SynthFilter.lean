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
  gX — Audio Synth Filter Invariants

  Salvaged from gameX lean/GameXProofs/SynthFilter.lean, re-verified
  against src/audio/synth.c:
    - filterMode NONE → input passes through              (52)
    - f = 2·sin(π·cutoff), clamped to ≤ 1                (54-55)
    - q = 1 − filterRes, guarded to ≥ 0.001              (56-57)
    - hp = input − LP − q·BP; BP += f·hp; LP += f·BP      (60-62)
    - modCutoff = cutoff + lfoValue·depth·0.3,
      clamped to [0.001, 0.999]                           (253-255)
    - LFO waveforms sine/square/sawtooth/triangle        (120-129)

  gX addition over the gameX spec: filter_f_clamped_le_one pins the
  `if (f > 1.0f) f = 1.0f` stability clamp the gameX spec never modeled.

  Theorems proven: 13
    - filter_f_bound:          f = 2·sin(π·cutoff) ∈ [0, 2] for cutoff ∈ [0,1]
    - filter_f_nonneg:         f ≥ 0 for cutoff ∈ [0, 1]
    - filter_f_clamped_le_one: min f 1 ≤ 1 (the gX stability clamp)
    - resonance_guarded:       q = max(1 − res, 0.001) ≥ 0.001
    - resonance_le_one:        q ≤ 1 for res ∈ [0, 1]
    - cutoff_clamped_below:    modCutoff clamp keeps ≥ 0.001
    - cutoff_clamped_above:    modCutoff clamp keeps ≤ 0.999
    - lfo_sine_in_unit:        sin(phase·2π) ∈ [−1, 1]
    - lfo_triangle_in_unit:    4·|p−0.5| − 1 ∈ [−1, 1] for p ∈ [0,1]
    - lfo_square_in_unit:      phase < 0.5 ? 1 : −1 ∈ [−1, 1]
    - lfo_sawtooth_in_unit:    2·phase − 1 ∈ [−1, 1] for phase ∈ [0,1]
    - cutoff_clamped_range:    clamped cutoff ∈ [0.001, 0.999]

  Continuous math modeled over ℝ.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace GxProofsGfx.Audio.SynthFilter

-- =============================================================
-- 1. Filter coefficient
-- =============================================================

-- f = 2·sin(π·cutoff) (synth.c:54).
noncomputable def filterF (cutoff : ℝ) : ℝ :=
  2 * Real.sin (Real.pi * cutoff)

-- f ≥ 0 for cutoff ∈ [0, 1] (sin ≥ 0 on [0, π]).
theorem filter_f_nonneg (cutoff : ℝ) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ 1) :
    0 ≤ filterF cutoff := by
  unfold filterF
  have hpi : 0 ≤ Real.pi * cutoff := mul_nonneg Real.pi_pos.le h0
  have hpi2 : Real.pi * cutoff ≤ Real.pi := by
    rw [mul_comm Real.pi cutoff]
    have : cutoff ≤ 1 := h1
    nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le]
  have hsin : 0 ≤ Real.sin (Real.pi * cutoff) := by
    exact Real.sin_nonneg_of_mem_Icc ⟨hpi, hpi2⟩
  nlinarith

-- f ≤ 2 (sin ≤ 1 always).
theorem filter_f_le_two (cutoff : ℝ) :
    filterF cutoff ≤ 2 := by
  unfold filterF
  have hsin : Real.sin (Real.pi * cutoff) ≤ 1 := Real.sin_le_one (Real.pi * cutoff)
  have hmul : 2 * Real.sin (Real.pi * cutoff) ≤ 2 * 1 := by
    exact mul_le_mul_of_nonneg_left hsin (by norm_num)
  simpa using hmul

-- f ∈ [0, 2] for cutoff ∈ [0, 1].
theorem filter_f_bound (cutoff : ℝ) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ 1) :
    0 ≤ filterF cutoff ∧ filterF cutoff ≤ 2 := by
  constructor
  · exact filter_f_nonneg cutoff h0 h1
  · exact filter_f_le_two cutoff

-- gX stability clamp (synth.c:55): `if (f > 1.0f) f = 1.0f`.
theorem filter_f_clamped_le_one (cutoff : ℝ) :
    min (filterF cutoff) 1 ≤ 1 := by
  exact min_le_right _ _

-- =============================================================
-- 2. Resonance
-- =============================================================

-- q = max(1 − filterRes, 0.001) (synth.c:56-57).
noncomputable def resonance (filterRes : ℝ) : ℝ :=
  max (1 - filterRes) 0.001

-- Resonance is always ≥ 0.001 (the self-oscillation guard).
theorem resonance_guarded (filterRes : ℝ) :
    0.001 ≤ resonance filterRes := by
  unfold resonance
  exact le_max_right _ _

-- For filterRes ≥ 0, q ≤ 1 (never amplifies beyond flat).
theorem resonance_le_one (filterRes : ℝ) (h0 : 0 ≤ filterRes) :
    resonance filterRes ≤ 1 := by
  unfold resonance
  apply max_le
  · linarith
  · norm_num

-- =============================================================
-- 3. LFO cutoff modulation
-- =============================================================

-- Clamped modulated cutoff (synth.c:254-255).
noncomputable def clampCutoff (c : ℝ) : ℝ :=
  max (min c 0.999) 0.001

-- The clamp keeps cutoff ≥ 0.001.
theorem cutoff_clamped_below (c : ℝ) :
    0.001 ≤ clampCutoff c := by
  unfold clampCutoff
  exact le_max_right _ _

-- The clamp keeps cutoff ≤ 0.999.
theorem cutoff_clamped_above (c : ℝ) :
    clampCutoff c ≤ 0.999 := by
  unfold clampCutoff
  apply max_le
  · exact min_le_right c 0.999
  · norm_num

-- The clamped value is within [0.001, 0.999].
theorem cutoff_clamped_range (c : ℝ) :
    0.001 ≤ clampCutoff c ∧ clampCutoff c ≤ 0.999 := by
  constructor
  · exact cutoff_clamped_below c
  · exact cutoff_clamped_above c

-- =============================================================
-- 4. LFO waveforms
-- =============================================================

-- Sine LFO (synth.c:120): sin(phase·2π) ∈ [−1, 1].
theorem lfo_sine_in_unit (phase : ℝ) :
    -1 ≤ Real.sin (phase * 2 * Real.pi) ∧ Real.sin (phase * 2 * Real.pi) ≤ 1 := by
  have h1 : -1 ≤ Real.sin (phase * 2 * Real.pi) :=
    Real.neg_one_le_sin (phase * 2 * Real.pi)
  have h2 : Real.sin (phase * 2 * Real.pi) ≤ 1 :=
    Real.sin_le_one (phase * 2 * Real.pi)
  constructor
  · exact h1
  · exact h2

-- Triangle LFO (synth.c:129): 4·|phase − 0.5| − 1 ∈ [−1, 1] for phase ∈ [0,1].
theorem lfo_triangle_in_unit (phase : ℝ) (h0 : 0 ≤ phase) (h1 : phase ≤ 1) :
    -1 ≤ 4 * |phase - 0.5| - 1 ∧ 4 * |phase - 0.5| - 1 ≤ 1 := by
  have habs : |phase - 0.5| ≤ 0.5 := by
    rw [abs_le]
    constructor
    · -- -0.5 ≤ phase - 0.5
      linarith
    · -- phase - 0.5 ≤ 0.5
      linarith
  constructor
  · have hnon : 0 ≤ 4 * |phase - 0.5| := by positivity
    linarith
  · have hmul : 4 * |phase - 0.5| ≤ 2 := by
      have h2 : 4 * |phase - 0.5| ≤ 4 * 0.5 := by
        exact mul_le_mul_of_nonneg_left habs (by norm_num)
      nlinarith
    linarith

-- Square LFO (synth.c:123): phase < 0.5 ? 1 : −1 ∈ [−1, 1].
theorem lfo_square_in_unit (phase : ℝ) :
    -1 ≤ (if phase < 0.5 then 1 else -1) ∧
    (if phase < 0.5 then 1 else -1) ≤ 1 := by
  by_cases h : phase < 0.5
  · simp [h]
  · simp [h]

-- Sawtooth LFO (synth.c:126): 2·phase − 1 ∈ [−1, 1] for phase ∈ [0,1].
theorem lfo_sawtooth_in_unit (phase : ℝ) (h0 : 0 ≤ phase) (h1 : phase ≤ 1) :
    -1 ≤ 2 * phase - 1 ∧ 2 * phase - 1 ≤ 1 := by
  constructor
  · linarith
  · linarith

end GxProofsGfx.Audio.SynthFilter
