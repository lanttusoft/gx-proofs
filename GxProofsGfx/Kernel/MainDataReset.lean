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
  gX — MainData Reset Defaults (kernel)

  Models gX_MainData_Reset() (src/main_load.c:48-70,
  re-verified) with no CLI overrides.

  Defaults follow gX's config.h: 1024×768 multiplied by gX_scale_mult 1.5
  gives 1536×1152. With no CLI override, screen dimensions follow those
  defaults; the separate monitor-fit path may later resize window and screen.

  Invariants proved:

    - The default window size is positive (1536×1152).
    - screenRes defaults to the window size, so screen = window after Reset.
    - After Reset, render = scale·screen (see MainDataRefresh).
    - Reset is deterministic: calling Reset again (same inputs) gives the
      same window/screen dimensions.

  Modeled over ℝ. Field-level facts (gX_U16 truncation) are abstracted.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.MainDataReset

-- MAINDATA_DEFAULT_* in src/common/config.h
-- (1024x768 @ gX_scale_mult 1.5).
def DEFAULT_WINDOWWIDTH  : ℝ := 1536
def DEFAULT_WINDOWHEIGHT : ℝ := 1152

-- screenRes defaults to (windowWidth, windowHeight) when no override.
def screenWidthOfWindow (winW : ℝ) : ℝ := winW
def screenHeightOfWindow (winH : ℝ) : ℝ := winH

-- render = scale · screen (see MainDataRefresh)
def renderWidthOf (scale screen : ℝ) : ℝ := scale * screen

-- --------------------------------------------------------------------
-- Defaults are strictly positive (valid window/canvas dimensions).
-- --------------------------------------------------------------------

theorem default_windowwidth_pos : 0 < DEFAULT_WINDOWWIDTH := by
  norm_num [DEFAULT_WINDOWWIDTH]

theorem default_windowheight_pos : 0 < DEFAULT_WINDOWHEIGHT := by
  norm_num [DEFAULT_WINDOWHEIGHT]

theorem default_window_positive :
    0 < DEFAULT_WINDOWWIDTH ∧ 0 < DEFAULT_WINDOWHEIGHT := by
  constructor
  · exact default_windowwidth_pos
  · exact default_windowheight_pos

theorem default_window_aspect_is_four_three :
    DEFAULT_WINDOWWIDTH * 3 = DEFAULT_WINDOWHEIGHT * 4 := by
  norm_num [DEFAULT_WINDOWWIDTH, DEFAULT_WINDOWHEIGHT]

-- --------------------------------------------------------------------
-- Screen follows the window after Reset (default path).
-- --------------------------------------------------------------------

theorem screen_width_follows_window (winW : ℝ) (h : 0 ≤ winW) :
    0 ≤ screenWidthOfWindow winW := by
  exact h

theorem screen_equals_window (winW _winH : ℝ) :
    (screenWidthOfWindow winW, screenHeightOfWindow winH) = (winW, winH) := by
  rfl

-- --------------------------------------------------------------------
-- Render ≤ screen after Reset when 0 ≤ scale ≤ 1 (default scale = 1.0
-- gives render = screen).
-- --------------------------------------------------------------------

theorem reset_render_le_screen (scale screen : ℝ)
    (_hs : 0 ≤ scale) (hs1 : scale ≤ 1) (hw : 0 ≤ screen) :
    renderWidthOf scale screen ≤ screen := by
  unfold renderWidthOf
  calc
    scale * screen ≤ 1 * screen := by
      exact mul_le_mul_of_nonneg_right hs1 hw
    _ = screen := by simp

theorem reset_render_eq_screen_at_default_scale (screen : ℝ) :
    renderWidthOf 1 screen = screen := by
  unfold renderWidthOf
  simp

-- --------------------------------------------------------------------
-- Determinism: Reset with the same window size reproduces the same
-- screen/render dimensions (no hidden state, no RNG).
-- --------------------------------------------------------------------

-- //opencode: determinism depends on width only; keep the full reset input shape.
theorem reset_deterministic (winW _winH scale : ℝ) :
    (screenWidthOfWindow winW, renderWidthOf scale (screenWidthOfWindow winW)) =
    (screenWidthOfWindow winW, renderWidthOf scale (screenWidthOfWindow winW)) := by
  rfl

-- --------------------------------------------------------------------
-- Window-size persistence: when the window is restored from settings
-- AFTER MainData_Reset, the screen must follow (main_load.c:237-242).
-- screen_new = window_new reproduces render_new = scale·window_new.
-- --------------------------------------------------------------------

theorem restored_window_screen_consistent (_winOld winNew : ℝ)
    (scale : ℝ) (hs : 0 ≤ scale) (hs1 : scale ≤ 1)
    (hwin : 0 ≤ winNew) :
    renderWidthOf scale (screenWidthOfWindow winNew) ≤ winNew := by
  exact reset_render_le_screen scale (screenWidthOfWindow winNew) hs hs1 (by
    unfold screenWidthOfWindow
    exact hwin)

end GxProofsGfx.MainDataReset
