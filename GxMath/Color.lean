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
  gX — per-channel contracts for src/gxmath/color.c.
  //ai: exact-real arithmetic with explicit truncation toward zero.

  lerpChannel truncates the signed delta BEFORE adding the source channel,
  then clamps to [0,255]. normalizeChannel and multiplyChannel model the
  normalized multiply/rescale path, with truncation on nonnegative output.
  C correspondence assumes finite inputs and representable float-to-I32
  casts/additions. IEEE rounding and undefined out-of-range casts are not
  certified; ideal byte round trips do not assert float byte round trips.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace GxMath.Color

def validChannel (a : ℤ) : Prop := 0 ≤ a ∧ a ≤ 255

def clampChannel (a : ℤ) : ℤ := min 255 (max 0 a)

noncomputable def truncate (x : ℝ) : ℤ :=
  if 0 ≤ x then ⌊x⌋ else ⌈x⌉

noncomputable def lerpChannel (a b : ℤ) (t : ℝ) : ℤ :=
  clampChannel (a + truncate (t * ((b : ℝ) - (a : ℝ))))

noncomputable def normalizeChannel (a : ℤ) : ℝ := (a : ℝ) / 255

noncomputable def fromNormalized (x : ℝ) : ℤ := truncate (x * 255)

noncomputable def multiplyChannel (a b : ℤ) : ℤ :=
  fromNormalized (normalizeChannel a * normalizeChannel b)

theorem truncate_int (a : ℤ) : truncate (a : ℝ) = a := by
  simp [truncate]

theorem clamp_valid (a : ℤ) : validChannel (clampChannel a) := by
  unfold validChannel clampChannel
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem clamp_of_valid (a : ℤ) (h : validChannel a) : clampChannel a = a := by
  simp [clampChannel, max_eq_right h.1, min_eq_right h.2]

theorem lerp_valid (a b : ℤ) (t : ℝ) : validChannel (lerpChannel a b t) := by
  exact clamp_valid _

theorem lerp_zero (a b : ℤ) (h : validChannel a) : lerpChannel a b 0 = a := by
  simpa [lerpChannel, truncate] using clamp_of_valid a h

theorem lerp_one (a b : ℤ) (h : validChannel b) : lerpChannel a b 1 = b := by
  have ht : truncate ((b : ℝ) - (a : ℝ)) = b - a := by
    rw [← Int.cast_sub, truncate_int]
  simpa [lerpChannel, ht] using clamp_of_valid b h

theorem lerp_self (a : ℤ) (t : ℝ) (h : validChannel a) : lerpChannel a a t = a := by
  simpa [lerpChannel, truncate] using clamp_of_valid a h

theorem lerp_truncation_order : lerpChannel 10 9 (1 / 2) = 10 := by
  norm_num [lerpChannel, truncate, clampChannel]

theorem normalize_bounds (a : ℤ) (h : validChannel a) :
    0 ≤ normalizeChannel a ∧ normalizeChannel a ≤ 1 := by
  have h0 : (0 : ℝ) ≤ a := by exact_mod_cast h.1
  have h1 : (a : ℝ) ≤ 255 := by exact_mod_cast h.2
  unfold normalizeChannel
  constructor <;> linarith

theorem normalize_zero : normalizeChannel 0 = 0 := by
  norm_num [normalizeChannel]

theorem normalize_white : normalizeChannel 255 = 1 := by
  norm_num [normalizeChannel]

theorem normalized_roundtrip (a : ℤ) : fromNormalized (normalizeChannel a) = a := by
  simp [fromNormalized, normalizeChannel, truncate_int]

theorem multiply_eq_truncate (a b : ℤ) :
    multiplyChannel a b = truncate ((a : ℝ) * (b : ℝ) / 255) := by
  unfold multiplyChannel fromNormalized normalizeChannel
  congr 1
  ring

theorem multiply_valid (a b : ℤ) (ha : validChannel a) (hb : validChannel b) :
    validChannel (multiplyChannel a b) := by
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast ha.1
  have ha1 : (a : ℝ) ≤ 255 := by exact_mod_cast ha.2
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast hb.1
  have hb1 : (b : ℝ) ≤ 255 := by exact_mod_cast hb.2
  have h0 : (0 : ℝ) ≤ (a : ℝ) * (b : ℝ) / 255 := by positivity
  have h1 : (a : ℝ) * (b : ℝ) / 255 ≤ 255 := by
    nlinarith [mul_le_mul ha1 hb1 hb0 (by norm_num : (0 : ℝ) ≤ 255)]
  rw [multiply_eq_truncate]
  unfold validChannel truncate
  rw [if_pos h0]
  constructor
  · exact Int.floor_nonneg.mpr h0
  · have hf := Int.floor_le ((a : ℝ) * (b : ℝ) / 255)
    have : (⌊(a : ℝ) * (b : ℝ) / 255⌋ : ℝ) ≤ 255 := le_trans hf h1
    exact_mod_cast this

theorem multiply_zero (a : ℤ) : multiplyChannel a 0 = 0 := by
  norm_num [multiplyChannel, fromNormalized, normalizeChannel, truncate]

theorem multiply_white (a : ℤ) : multiplyChannel a 255 = a := by
  simpa [multiplyChannel, normalize_white] using normalized_roundtrip a

theorem multiply_comm (a b : ℤ) : multiplyChannel a b = multiplyChannel b a := by
  simp [multiplyChannel, mul_comm]

end GxMath.Color
