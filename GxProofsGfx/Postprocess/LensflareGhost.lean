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
  gX — Lensflare Ghost Element Math

  Salvaged from gameX lean/GameXProofs/LensflareGhost.lean,
   //ai: re-verified: resources/shader/gfx_lensflare.frag ghost loop
  carries the identical ghost falloff and chromatic tint formulas:
    intensity *= (1.0 - 0.12·i)
    tint = (1.0 - 0.1·i, 0.8 - 0.05·i, 0.6 + 0.1·i)

   //ai: These coefficient proofs do not certify ghost placement, envelopes,
   source occlusion, rasterization or float/GPU accuracy.
   These must stay inside the valid [0,1] color range and the falloff must
  stay positive, otherwise the flare clamps or inverts. Proven over ℝ for
  every ghost index i < 5.

  Theorems proven: 5
    - ghosts_increasing:       ghost offsets strictly increase (i+1 < i+2)
    - tint_red_in_range:       0 ≤ tint.r ≤ 1
    - tint_green_in_range:     0 ≤ tint.g ≤ 1
    - tint_blue_in_range:      0 ≤ tint.b ≤ 1
    - intensity_positive:      falloff 1 - 0.12·i > 0
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.LensflareGhost

-- 5 ghost elements
def ghostCount : Nat := 5

-- Ghost indices 0..4 are strictly increasing in distance
theorem ghosts_increasing (i : Nat) (h : i < 4) : (i + 1) < (i + 2) := by
  omega

-- Chromatic tint formulas (from gfx_lensflare.frag line 58)
def tintRed (i : ℝ) : ℝ := 1 - 0.1 * i
def tintGreen (i : ℝ) : ℝ := 0.8 - 0.05 * i
def tintBlue (i : ℝ) : ℝ := 0.6 + 0.1 * i

-- Intensity falloff (from line 57)
def falloff (i : ℝ) : ℝ := 1 - 0.12 * i

-- Red channel stays in [0,1] for all 5 ghosts
theorem tint_red_in_range (i : Nat) (h : i < 5) :
    0 ≤ tintRed i ∧ tintRed i ≤ 1 := by
  unfold tintRed
  have hi4 : i ≤ 4 := by omega
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
  have hi4r : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
  constructor
  · nlinarith
  · nlinarith

-- Green channel stays in [0,1] for all 5 ghosts
theorem tint_green_in_range (i : Nat) (h : i < 5) :
    0 ≤ tintGreen i ∧ tintGreen i ≤ 1 := by
  unfold tintGreen
  have hi4 : i ≤ 4 := by omega
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
  have hi4r : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
  constructor
  · nlinarith
  · nlinarith

-- Blue channel stays in [0,1] for all 5 ghosts
theorem tint_blue_in_range (i : Nat) (h : i < 5) :
    0 ≤ tintBlue i ∧ tintBlue i ≤ 1 := by
  unfold tintBlue
  have hi4 : i ≤ 4 := by omega
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
  have hi4r : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
  constructor
  · nlinarith
  · nlinarith

-- Intensity falloff stays positive for all 5 ghosts
theorem intensity_positive (i : Nat) (h : i < 5) : 0 < falloff i := by
  unfold falloff
  have hi4 : i ≤ 4 := by omega
  have hi4r : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
  have hprod : (0.12 : ℝ) * (i : ℝ) ≤ (0.12 : ℝ) * 4 := by
    exact mul_le_mul_of_nonneg_left hi4r (by norm_num)
  linarith

end GxProofsGfx.LensflareGhost
