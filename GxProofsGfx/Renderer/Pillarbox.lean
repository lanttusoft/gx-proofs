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
  gX — undocked viewport aspect-fit specification (Mathlib tier)

  Models the branch selector and box formulas in
  src/gui/gui.c:gX_GUI_Viewport_Refresh. The wide and tall branches
  require an aspect-ratio difference greater than 0.001; otherwise the code
  fills the entire window. Consequently exact aspect preservation applies to
  the two fit branches, while the full-window branch only guarantees an
  aspect-ratio error bounded by 0.001 in this exact-real model.

  This does not certify F32 comparison/division, pixel rounding, or rendering.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.Pillarbox

noncomputable def aspectEpsilon : ℝ := (1 : ℝ) / 1000
noncomputable def winAsp (ww wh : ℝ) : ℝ := ww / wh
noncomputable def gameAsp (gw gh : ℝ) : ℝ := gw / gh

def wideBranch (windowAspect gameAspect : ℝ) : Prop :=
  gameAspect + aspectEpsilon < windowAspect

def tallBranch (windowAspect gameAspect : ℝ) : Prop :=
  windowAspect + aspectEpsilon < gameAspect

def fullWindowBranch (windowAspect gameAspect : ℝ) : Prop :=
  ¬ wideBranch windowAspect gameAspect ∧ ¬ tallBranch windowAspect gameAspect

theorem aspect_epsilon_value : aspectEpsilon = 0.001 := by
  norm_num [aspectEpsilon]

theorem wide_and_tall_disjoint (windowAspect gameAspect : ℝ)
    (wide : wideBranch windowAspect gameAspect)
    (tall : tallBranch windowAspect gameAspect) : False := by
  unfold wideBranch tallBranch aspectEpsilon at *
  linarith

theorem full_window_aspect_error_bounded (windowAspect gameAspect : ℝ)
    (full : fullWindowBranch windowAspect gameAspect) :
    |windowAspect - gameAspect| ≤ aspectEpsilon := by
  simp only [fullWindowBranch, wideBranch, tallBranch] at full
  rcases full with ⟨notWide, notTall⟩
  have hnotWide : windowAspect ≤ gameAspect + aspectEpsilon :=
    le_of_not_gt notWide
  have hnotTall : gameAspect ≤ windowAspect + aspectEpsilon :=
    le_of_not_gt notTall
  unfold aspectEpsilon at notWide notTall hnotWide hnotTall ⊢
  rw [abs_le]
  constructor <;> linarith

-- Fit boxes: wide window uses full height; tall window uses full width.
theorem wide_aspect (_ww wh gw gh : ℝ) (hwh : 0 < wh) :
    (wh * gameAsp gw gh) / wh = gameAsp gw gh := by
  unfold gameAsp
  field_simp

theorem tall_aspect (ww _wh gw gh : ℝ) (hww : 0 < ww) :
    ww / (ww / gameAsp gw gh) = gameAsp gw gh := by
  have hww' : ww ≠ 0 := ne_of_gt hww
  field_simp

theorem wide_fits (ww wh gw gh : ℝ) (hwh : 0 < wh) (hgh : 0 < gh)
    (h : gameAsp gw gh < winAsp ww wh) :
    wh * gameAsp gw gh ≤ ww ∧ (ww - wh * gameAsp gw gh) / 2 ≥ 0 := by
  unfold gameAsp winAsp at h
  have hgne : gh ≠ 0 := ne_of_gt hgh
  have hpos : (0 : ℝ) < gh * wh := mul_pos hgh hwh
  have h2 : (gw / gh) * (gh * wh) < (ww / wh) * (gh * wh) :=
    mul_lt_mul_of_pos_right h hpos
  rw [show (gw / gh) * (gh * wh) = gw * wh by field_simp,
      show (ww / wh) * (gh * wh) = ww * gh by field_simp] at h2
  have hfit : wh * (gw / gh) ≤ ww := by
    rw [← mul_div_assoc, div_le_iff₀ hgh]
    have hc : gw * wh = wh * gw := mul_comm _ _
    linarith
  constructor
  · unfold gameAsp
    exact hfit
  · have : wh * gameAsp gw gh ≤ ww := hfit
    unfold gameAsp at this ⊢
    linarith

theorem tall_fits (ww wh gw gh : ℝ) (hwh : 0 < wh) (hsa : 0 < gameAsp gw gh)
    (h : winAsp ww wh < gameAsp gw gh) :
    ww / gameAsp gw gh ≤ wh ∧ (wh - ww / gameAsp gw gh) / 2 ≥ 0 := by
  unfold gameAsp winAsp at h
  rw [div_lt_iff₀ hwh] at h
  have hfit : ww / (gw / gh) ≤ wh := by
    rw [div_le_iff₀ (by unfold gameAsp at hsa; exact hsa)]
    have hc : (gw / gh) * wh = wh * (gw / gh) := mul_comm _ _
    linarith
  constructor
  · unfold gameAsp
    exact hfit
  · have : ww / gameAsp gw gh ≤ wh := hfit
    unfold gameAsp at this ⊢
    linarith

theorem wide_branch_fits (ww wh gw gh : ℝ) (hwh : 0 < wh) (hgh : 0 < gh)
    (wide : wideBranch (winAsp ww wh) (gameAsp gw gh)) :
    wh * gameAsp gw gh ≤ ww := by
  have h : gameAsp gw gh < winAsp ww wh := by
    unfold wideBranch aspectEpsilon at wide
    linarith
  exact (wide_fits ww wh gw gh hwh hgh h).1

theorem tall_branch_fits (ww wh gw gh : ℝ) (hwh : 0 < wh)
    (hsa : 0 < gameAsp gw gh)
    (tall : tallBranch (winAsp ww wh) (gameAsp gw gh)) :
    ww / gameAsp gw gh ≤ wh := by
  have h : winAsp ww wh < gameAsp gw gh := by
    unfold tallBranch aspectEpsilon at tall
    linarith
  exact (tall_fits ww wh gw gh hwh hsa h).1

theorem fullbox_fits (ww wh : ℝ) : ww ≤ ww ∧ wh ≤ wh ∧
    (ww - ww) / 2 = 0 ∧ (wh - wh) / 2 = 0 :=
  ⟨le_refl _, le_refl _, by ring, by ring⟩

theorem full_window_branch_can_distort_aspect :
    fullWindowBranch (1 + 1 / 2000) 1 ∧ (1 + 1 / 2000 : ℝ) ≠ 1 := by
  constructor
  · constructor
    · unfold wideBranch aspectEpsilon
      norm_num
    · unfold tallBranch aspectEpsilon
      norm_num
  · norm_num

end GxProofsGfx.Pillarbox
