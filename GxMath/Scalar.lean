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
  gxmath/Scalar.lean
  gX — a game engine

  Formal contracts for the real-valued scalar helpers in
  src/gxmath/scalar.c.

  The model is over ℝ. It does not certify IEEE floor/rounding, the integer
  factorial/GCD/combinatorics helpers, or the tolerance-based equality
  predicates; those remain numeric property-test targets.

  Theorems proven:
    - clamp bounds, idempotence, and the low/high saturation cases
    - lerp endpoints
    - normalize/lerp inverse round trips
    - remap as lerp of normalize, plus its endpoint values
    - floor-based wrap range and whole-period invariance for an increasing interval
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxMath
namespace Scalar

def clamp (value low high : ℝ) : ℝ :=
  max low (min high value)

def lerp (start finish amount : ℝ) : ℝ :=
  start + amount * (finish - start)

noncomputable def normalize (value start finish : ℝ) : ℝ :=
  (value - start) / (finish - start)

noncomputable def remap (value inputStart inputEnd outputStart outputEnd : ℝ) : ℝ :=
  (value - inputStart) / (inputEnd - inputStart) *
    (outputEnd - outputStart) + outputStart

--ai: mirror the native quotient-floor formula over ℝ for a nonzero interval.
noncomputable def wrap (value low high : ℝ) : ℝ :=
  value - (high - low) * (Int.floor ((value - low) / (high - low)) : ℝ)

theorem clamp_between (value low high : ℝ) (h : low ≤ high) :
    low ≤ clamp value low high ∧ clamp value low high ≤ high := by
  unfold clamp
  constructor
  · exact le_max_left low (min high value)
  · exact max_le h (min_le_left high value)

theorem clamp_of_between (value low high : ℝ)
    (hLow : low ≤ value) (hHigh : value ≤ high) :
    clamp value low high = value := by
  unfold clamp
  rw [min_eq_right hHigh, max_eq_right hLow]

theorem clamp_idempotent (value low high : ℝ) (h : low ≤ high) :
    clamp (clamp value low high) low high = clamp value low high := by
  apply clamp_of_between
  · exact (clamp_between value low high h).1
  · exact (clamp_between value low high h).2

theorem clamp_of_le_low (value low high : ℝ) (hLow : low ≤ high)
    (h : value ≤ low) :
    clamp value low high = low := by
  unfold clamp
  have hMin : min high value = value := min_eq_right (le_trans h hLow)
  rw [hMin, max_eq_left h]

theorem clamp_of_high_le (value low high : ℝ) (hLow : low ≤ high)
    (h : high ≤ value) :
    clamp value low high = high := by
  unfold clamp
  rw [min_eq_left h, max_eq_right hLow]

theorem clamp_low (low high : ℝ) (h : low ≤ high) :
    clamp low low high = low := by
  apply clamp_of_between <;> linarith

theorem clamp_high (low high : ℝ) (h : low ≤ high) :
    clamp high low high = high := by
  apply clamp_of_between <;> linarith

theorem lerp_zero (start finish : ℝ) :
    lerp start finish 0 = start := by
  simp [lerp]

theorem lerp_one (start finish : ℝ) :
    lerp start finish 1 = finish := by
  unfold lerp
  ring

theorem normalize_lerp (start finish amount : ℝ)
    (h : finish - start ≠ 0) :
    normalize (lerp start finish amount) start finish = amount := by
  unfold normalize lerp
  field_simp [h]
  ring

theorem lerp_normalize (value start finish : ℝ)
    (h : finish - start ≠ 0) :
    lerp start finish (normalize value start finish) = value := by
  unfold normalize lerp
  field_simp [h]
  ring

theorem remap_eq_lerp_normalize (value inputStart inputEnd outputStart outputEnd : ℝ) :
    remap value inputStart inputEnd outputStart outputEnd =
      lerp outputStart outputEnd (normalize value inputStart inputEnd) := by
  unfold remap lerp normalize
  ring

theorem remap_start (inputStart inputEnd outputStart outputEnd : ℝ)
    (h : inputEnd - inputStart ≠ 0) :
    remap inputStart inputStart inputEnd outputStart outputEnd = outputStart := by
  unfold remap
  field_simp [h]
  ring

theorem remap_end (inputStart inputEnd outputStart outputEnd : ℝ)
    (h : inputEnd - inputStart ≠ 0) :
    remap inputEnd inputStart inputEnd outputStart outputEnd = outputEnd := by
  unfold remap
  field_simp [h]
  ring

--ai: the native floor remainder is lower-inclusive and upper-exclusive when high exceeds low.
theorem wrap_range (value low high : ℝ) (h : low < high) :
    low ≤ wrap value low high ∧ wrap value low high < high := by
  let period := high - low
  let turns : ℤ := Int.floor ((value - low) / period)
  have hperiod : 0 < period := sub_pos.mpr h
  have hturnsLow : (turns : ℝ) ≤ (value - low) / period := by
    exact Int.floor_le _
  have hturnsHigh : (value - low) / period < (turns : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hscaledLow : (turns : ℝ) * period ≤ value - low :=
    (le_div_iff₀ hperiod).mp hturnsLow
  have hscaledHigh : value - low < ((turns : ℝ) + 1) * period :=
    (div_lt_iff₀ hperiod).mp hturnsHigh
  have hwrapped : wrap value low high = value - period * (turns : ℝ) := by
    simp [wrap, period, turns]
  rw [hwrapped]
  constructor
  · calc
      low ≤ value - (turns : ℝ) * period := by linarith
      _ = value - period * (turns : ℝ) := by ring
  · calc
      value - period * (turns : ℝ) < low + period := by nlinarith [hscaledHigh]
      _ = high := by dsimp [period]; ring

--ai: adding an integral number of interval widths leaves the wrapped value unchanged.
theorem wrap_add_period (value low high : ℝ) (turns : ℤ) (h : low < high) :
    wrap (value + (turns : ℝ) * (high - low)) low high = wrap value low high := by
  have hperiod : high - low ≠ 0 := ne_of_gt (sub_pos.mpr h)
  have hquotient :
      (value + (turns : ℝ) * (high - low) - low) / (high - low) =
        (value - low) / (high - low) + turns := by
    field_simp [hperiod]
    ring
  unfold wrap
  rw [hquotient, Int.floor_add_intCast]
  push_cast
  ring

end Scalar
end GxMath
