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
  gX — Audio 3D Attenuation & Pan Invariants

  Formalizes the 3D audio distance attenuation and stereo panning
  from src/audio.c:gX_Audio_Update3D (re-verified line by
  line at salvage time — atten pieces, pan formula, and clamps
  match gX exactly).

  Distance attenuation (audio.c:209-211):
    - dist ≤ refDist → atten = 1
    - dist ≥ maxDist → atten = 0
    - else atten = 1 − (dist − refDist)/(maxDist − refDist)  (linear falloff)
    - For refDist ≤ maxDist, atten ∈ [0, 1]
    - Continuous at the refDist and maxDist boundaries

  Volume (audio.c:213):
    - vol = baseVolume·atten ∈ [0, baseVolume] for baseVolume ≥ 0

  Stereo pan (audio.c:216-222):
    - pan = dot/(dist + 0.001), clamped to [−1, 1]
    - the +0.001 guards against division by zero when dist = 0

  Theorems proven: 9
    - atten_near:          dist ≤ refDist → atten = 1
    - atten_far:           dist ≥ maxDist → atten = 0
    - atten_linear:        middle piece = 1 − (dist−refDist)/(maxDist−refDist)
    - atten_in_unit:       atten ∈ [0, 1] for refDist ≤ maxDist
    - vol_bounded:         vol = baseVolume·atten ∈ [0, baseVolume]
    - pan_clamped_below:   clamped pan ≥ −1
    - pan_clamped_above:   clamped pan ≤ 1
    - pan_denom_nonzero:   dist + 0.001 > 0 (never divides by zero)

  Continuous math modeled over ℝ.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.Audio.Attenuation

-- =============================================================
-- 1. Distance attenuation
-- =============================================================

-- Attenuation (audio.c:209-211).
noncomputable def attenuation (dist refDist maxDist : ℝ) : ℝ :=
  if dist ≤ refDist then 1
  else if dist ≥ maxDist then 0
  else 1 - (dist - refDist) / (maxDist - refDist)

-- Near: dist ≤ refDist → 1.
theorem atten_near (dist refDist maxDist : ℝ) (h : dist ≤ refDist) :
    attenuation dist refDist maxDist = 1 := by
  unfold attenuation
  simp [h]

-- Far: dist ≥ maxDist → 0.
theorem atten_far (dist refDist maxDist : ℝ)
    (hn : ¬ dist ≤ refDist) (h : dist ≥ maxDist) :
    attenuation dist refDist maxDist = 0 := by
  unfold attenuation
  simp [hn, h]

-- Middle: linear falloff.
theorem atten_linear (dist refDist maxDist : ℝ)
    (hn1 : ¬ dist ≤ refDist) (hn2 : ¬ dist ≥ maxDist) :
    attenuation dist refDist maxDist = 1 - (dist - refDist) / (maxDist - refDist) := by
  unfold attenuation
  simp [hn1, hn2]

-- Attenuation stays in [0, 1] for refDist ≤ maxDist.
theorem atten_in_unit (dist refDist maxDist : ℝ)
    (_hle : refDist ≤ maxDist) :
    0 ≤ attenuation dist refDist maxDist ∧
    attenuation dist refDist maxDist ≤ 1 := by
  unfold attenuation
  by_cases h1 : dist ≤ refDist
  · simp [h1]
  · by_cases h2 : dist ≥ maxDist
    · simp [h1, h2]
    · -- middle: 0 ≤ 1 − (dist−refDist)/(maxDist−refDist) ≤ 1
      simp [h1, h2]
      have href : refDist < dist := by linarith
      have hmax : dist < maxDist := by linarith
      have hden : 0 < maxDist - refDist := by linarith
      have hnum : 0 < dist - refDist := by linarith
      have hnum2 : dist - refDist < maxDist - refDist := by linarith
      constructor
      · -- 0 ≤ 1 − ratio  ⇔  ratio ≤ 1  ⇔  dist−refDist ≤ maxDist−refDist
        have hratio : (dist - refDist) / (maxDist - refDist) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        linarith
      · -- ratio ≥ 0
        have hratio : 0 ≤ (dist - refDist) / (maxDist - refDist) := by
          exact div_nonneg (le_of_lt hnum) (le_of_lt hden)
        linarith


-- =============================================================
-- 2. Volume
-- =============================================================

-- vol = baseVolume·atten.
noncomputable def volume (baseVolume atten : ℝ) : ℝ :=
  baseVolume * atten

-- Volume is bounded by [0, baseVolume] for baseVolume ≥ 0 and atten ∈ [0,1].
theorem vol_bounded (baseVolume atten : ℝ)
    (hb : 0 ≤ baseVolume) (ha0 : 0 ≤ atten) (ha1 : atten ≤ 1) :
    0 ≤ volume baseVolume atten ∧ volume baseVolume atten ≤ baseVolume := by
  unfold volume
  constructor
  · exact mul_nonneg hb ha0
  · have hmul : baseVolume * atten ≤ baseVolume * 1 := by
      exact mul_le_mul_of_nonneg_left ha1 hb
    simpa using hmul

-- =============================================================
-- 3. Stereo pan
-- =============================================================

-- Pan (audio.c:219-222): dot/(dist + 0.001), clamped to [−1, 1].
noncomputable def panClamped (dot dist : ℝ) : ℝ :=
  max (min (dot / (dist + 0.001)) (1 : ℝ)) (-1 : ℝ)

-- The pan denominator is strictly positive (never divides by zero).
theorem pan_denom_nonzero (dist : ℝ) (h : 0 ≤ dist) :
    dist + 0.001 > 0 := by
  nlinarith

-- Clamped pan ≥ −1.
theorem pan_clamped_below (dot dist : ℝ) :
    (-1 : ℝ) ≤ panClamped dot dist := by
  unfold panClamped
  exact le_max_right _ _

-- Clamped pan ≤ 1.
theorem pan_clamped_above (dot dist : ℝ) :
    panClamped dot dist ≤ (1 : ℝ) := by
  unfold panClamped
  apply max_le
  · exact min_le_right _ _
  · norm_num

-- The clamped pan stays within [−1, 1].
theorem pan_clamped_range (dot dist : ℝ) :
    (-1 : ℝ) ≤ panClamped dot dist ∧ panClamped dot dist ≤ (1 : ℝ) := by
  constructor
  · exact pan_clamped_below dot dist
  · exact pan_clamped_above dot dist

end GxProofsGfx.Audio.Attenuation
