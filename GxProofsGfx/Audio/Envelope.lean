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
  gX — Audio Synth ADSR Envelope Invariants

  Salvaged from gameX lean/GameXProofs/AudioEnvelope.lean, re-verified
  step by step against src/audio/synth.c:264-298:
    - ATTACK:  step = 1 / (attackTime*sampleRate + 1),
               envelope += step; clamp to 1 → DECAY      (267-272)
    - DECAY:   step = (1 - sustainLevel) / (decayTime*sampleRate + 1),
               envelope -= step; clamp to sustainLevel → SUSTAIN (276-281)
    - RELEASE: step = releaseLevel / (releaseTime*sampleRate + 1),
               envelope -= step; clamp to 0 → OFF         (286-293)

  Theorems proven: 15
    - attack_step_pos:             attack step is strictly positive
    - attack_step_le_one:          attack step never exceeds 1
    - decay_step_nonneg:           decay step is non-negative
    - release_step_nonneg:         release step is non-negative
    - decay_step_le_one_minus_sustain: decay step never overshoots
                                  sustainLevel
    - release_step_le_releaseLevel:    release step never overshoots
                                  releaseLevel
    - attack_env_nonneg:           attack-clamped envelope stays ≥ 0
    - attack_env_le_one:           attack-clamped envelope stays ≤ 1
    - decay_env_ge_sustain:        decay-clamped envelope stays ≥ sustainLevel
    - decay_env_le_one:            decay-clamped envelope stays ≤ 1
    - release_env_nonneg:          release-clamped envelope stays ≥ 0
    - release_env_le_one:          release-clamped envelope stays ≤ 1
    - attack_reaches_one:          envelope clamps to exactly 1 at attack end
    - decay_reaches_sustain:       envelope clamps to exactly sustainLevel
    - release_reaches_zero:        envelope clamps to exactly 0 at release end

  Continuous math is modeled over ℝ. sampleRate ≥ 0, times ≥ 0,
  sustainLevel ∈ [0,1], releaseLevel ≥ 0, envelope ∈ [0,1].

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.Audio.Envelope

-- Per-sample step sizes (synth.c). The +1 in the denominator guards
-- against a zero divisor.
noncomputable def attackStep (attackTime sampleRate : ℝ) : ℝ :=
  1 / (attackTime * sampleRate + 1)

noncomputable def decayStep (decayTime sampleRate sustainLevel : ℝ) : ℝ :=
  (1 - sustainLevel) / (decayTime * sampleRate + 1)

noncomputable def releaseStep (releaseTime sampleRate releaseLevel : ℝ) : ℝ :=
  releaseLevel / (releaseTime * sampleRate + 1)

-- Clamped envelope after one sample in each stage, mirroring the C code.
noncomputable def attackEnv (env attackTime sampleRate : ℝ) : ℝ :=
  min (env + attackStep attackTime sampleRate) 1

noncomputable def decayEnv (env decayTime sampleRate sustainLevel : ℝ) : ℝ :=
  max (env - decayStep decayTime sampleRate sustainLevel) sustainLevel

noncomputable def releaseEnv (env releaseTime sampleRate releaseLevel : ℝ) : ℝ :=
  max (env - releaseStep releaseTime sampleRate releaseLevel) 0

-- Helper: for 0 ≤ a and 1 ≤ d, dividing by d never increases a.
private lemma div_le_self_of_ge_one (a d : ℝ) (ha : 0 ≤ a) (hd : 1 ≤ d) :
    a / d ≤ a := by
  rw [div_eq_mul_inv]
  have hdpos : 0 < d := by linarith
  have hinv : d⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ hdpos zero_lt_one).mpr hd
  exact mul_le_of_le_one_right ha hinv

-- =============================================================
-- 1. Step sizes
-- =============================================================

-- ATTACK: 1 / (attackTime*sampleRate + 1) > 0 since the +1 makes the
-- denominator strictly positive.
theorem attack_step_pos {attackTime sampleRate : ℝ}
    (hA : 0 ≤ attackTime) (hR : 0 ≤ sampleRate) :
    0 < attackStep attackTime sampleRate := by
  unfold attackStep
  positivity

-- ATTACK: denominator ≥ 1, so the step is ≤ 1.
theorem attack_step_le_one {attackTime sampleRate : ℝ}
    (hA : 0 ≤ attackTime) (hR : 0 ≤ sampleRate) :
    attackStep attackTime sampleRate ≤ 1 := by
  unfold attackStep
  have hd : 1 ≤ attackTime * sampleRate + 1 := by nlinarith
  have hdpos : 0 < attackTime * sampleRate + 1 := by nlinarith [mul_nonneg hA hR]
  have hinv : (attackTime * sampleRate + 1)⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ hdpos zero_lt_one).mpr hd
  simpa using hinv

-- DECAY: numerator (1 - sustainLevel) ≥ 0 when sustainLevel ≤ 1.
theorem decay_step_nonneg {decayTime sampleRate sustainLevel : ℝ}
    (hT : 0 ≤ decayTime) (hR : 0 ≤ sampleRate) (hS : sustainLevel ≤ 1) :
    0 ≤ decayStep decayTime sampleRate sustainLevel := by
  unfold decayStep
  have hdpos : 0 < decayTime * sampleRate + 1 := by nlinarith [mul_nonneg hT hR]
  exact div_nonneg (by linarith) (le_of_lt hdpos)

-- RELEASE: numerator releaseLevel ≥ 0.
theorem release_step_nonneg {releaseTime sampleRate releaseLevel : ℝ}
    (hT : 0 ≤ releaseTime) (hR : 0 ≤ sampleRate) (hL : 0 ≤ releaseLevel) :
    0 ≤ releaseStep releaseTime sampleRate releaseLevel := by
  unfold releaseStep
  have hdpos : 0 < releaseTime * sampleRate + 1 := by nlinarith [mul_nonneg hT hR]
  exact div_nonneg hL (le_of_lt hdpos)

-- DECAY: step ≤ 1 - sustainLevel (dividing by denominator ≥ 1 shrinks).
theorem decay_step_le_one_minus_sustain {decayTime sampleRate sustainLevel : ℝ}
    (hT : 0 ≤ decayTime) (hR : 0 ≤ sampleRate) (hS : sustainLevel ≤ 1) :
    decayStep decayTime sampleRate sustainLevel ≤ 1 - sustainLevel := by
  unfold decayStep
  exact div_le_self_of_ge_one (1 - sustainLevel) (decayTime * sampleRate + 1)
    (by linarith) (by nlinarith)

-- RELEASE: step ≤ releaseLevel.
theorem release_step_le_releaseLevel {releaseTime sampleRate releaseLevel : ℝ}
    (hT : 0 ≤ releaseTime) (hR : 0 ≤ sampleRate) (hL : 0 ≤ releaseLevel) :
    releaseStep releaseTime sampleRate releaseLevel ≤ releaseLevel := by
  unfold releaseStep
  exact div_le_self_of_ge_one releaseLevel (releaseTime * sampleRate + 1)
    hL (by nlinarith)

-- =============================================================
-- 2. Envelope stays in [0, 1] in every stage
-- =============================================================

-- ATTACK: envelope + step ≥ 0 when the envelope starts ≥ 0.
theorem attack_env_nonneg {env attackTime sampleRate : ℝ}
    (hE : 0 ≤ env) (hA : 0 ≤ attackTime) (hR : 0 ≤ sampleRate) :
    0 ≤ attackEnv env attackTime sampleRate := by
  unfold attackEnv
  have hs : 0 ≤ attackStep attackTime sampleRate :=
    le_of_lt (attack_step_pos hA hR)
  apply le_min
  · linarith
  · norm_num

-- ATTACK: clamped at 1, so never exceeds 1.
theorem attack_env_le_one {env attackTime sampleRate : ℝ} :
    attackEnv env attackTime sampleRate ≤ 1 := by
  unfold attackEnv
  exact min_le_right _ _

-- DECAY: clamped at sustainLevel from below, so never drops below it.
theorem decay_env_ge_sustain {env decayTime sampleRate sustainLevel : ℝ} :
    sustainLevel ≤ decayEnv env decayTime sampleRate sustainLevel := by
  unfold decayEnv
  exact le_max_right _ _

-- DECAY: stays ≤ 1 when the envelope starts ≤ 1 (subtracting a
-- non-negative step only lowers it).
theorem decay_env_le_one {env decayTime sampleRate sustainLevel : ℝ}
    (hE : env ≤ 1) (hT : 0 ≤ decayTime) (hR : 0 ≤ sampleRate) (hS : sustainLevel ≤ 1) :
    decayEnv env decayTime sampleRate sustainLevel ≤ 1 := by
  unfold decayEnv
  apply max_le
  · have hs : 0 ≤ decayStep decayTime sampleRate sustainLevel :=
      decay_step_nonneg hT hR hS
    linarith
  · exact hS

-- RELEASE: clamped at 0 from below.
theorem release_env_nonneg {env releaseTime sampleRate releaseLevel : ℝ} :
    0 ≤ releaseEnv env releaseTime sampleRate releaseLevel := by
  unfold releaseEnv
  exact le_max_right _ _

-- RELEASE: stays ≤ 1 when the envelope starts ≤ 1.
theorem release_env_le_one {env releaseTime sampleRate releaseLevel : ℝ}
    (hE : env ≤ 1) (hT : 0 ≤ releaseTime) (hR : 0 ≤ sampleRate) (hL : 0 ≤ releaseLevel) :
    releaseEnv env releaseTime sampleRate releaseLevel ≤ 1 := by
  unfold releaseEnv
  apply max_le
  · have hs : 0 ≤ releaseStep releaseTime sampleRate releaseLevel :=
      release_step_nonneg hT hR hL
    linarith
  · norm_num

-- =============================================================
-- 3. Stage transitions reach their targets exactly
-- =============================================================

-- ATTACK end: when envelope + step reaches 1, the clamp lands on 1.
theorem attack_reaches_one {env attackTime sampleRate : ℝ}
    (h : 1 ≤ env + attackStep attackTime sampleRate) :
    attackEnv env attackTime sampleRate = 1 := by
  unfold attackEnv
  exact min_eq_right h

-- DECAY end: when envelope - step reaches sustainLevel, clamp lands on it.
theorem decay_reaches_sustain {env decayTime sampleRate sustainLevel : ℝ}
    (h : env - decayStep decayTime sampleRate sustainLevel ≤ sustainLevel) :
    decayEnv env decayTime sampleRate sustainLevel = sustainLevel := by
  unfold decayEnv
  exact max_eq_right h

-- RELEASE end: when envelope - step reaches 0, clamp lands on 0.
theorem release_reaches_zero {env releaseTime sampleRate releaseLevel : ℝ}
    (h : env - releaseStep releaseTime sampleRate releaseLevel ≤ 0) :
    releaseEnv env releaseTime sampleRate releaseLevel = 0 := by
  unfold releaseEnv
  exact max_eq_right h

end GxProofsGfx.Audio.Envelope
