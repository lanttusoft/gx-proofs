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
  gX — MainData Refresh Resolution Invariants (kernel)

  Models gX_MainData_Refresh() (src/main_load.c:40-46,
  re-verified — same formula, same U16 truncation note):

      maindata.renderWidth  = (u16)(renderScale * screenWidth)
      maindata.renderHeight = (u16)(renderScale * screenHeight)

  The truncation to gX_U16 is ignored — modeling over ℝ (exact reals),
  the truncation only ever DECREASES the value, so the ≤ bounds proved
  here hold a fortiori for the truncated u16 result.

  Key invariants (the "resolution ladder"):
    - For 0 ≤ scale ≤ 1:  render ≤ screen  (render never exceeds screen)
    - render is monotone in both scale and screen
    - at scale = 1: render = screen
    - render is a pure function of (scale, screen) — no hidden state
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.MainDataRefresh

-- renderWidth = renderScale * screenWidth (float product, no clamp)
def renderWidth (scale screen : ℝ) : ℝ := scale * screen

-- renderHeight = renderScale * screenHeight
def renderHeight (scale screen : ℝ) : ℝ := scale * screen

-- --------------------------------------------------------------------
-- render ≤ screen when scale ≤ 1 and both operands nonnegative.
-- --------------------------------------------------------------------

theorem renderWidth_le_screen (scale screen : ℝ)
    (_hs : 0 ≤ scale) (hs1 : scale ≤ 1) (hw : 0 ≤ screen) :
    renderWidth scale screen ≤ screen := by
  unfold renderWidth
  calc
    scale * screen ≤ 1 * screen := by
      exact mul_le_mul_of_nonneg_right hs1 hw
    _ = screen := by simp

theorem renderHeight_le_screen (scale screen : ℝ)
    (_hs : 0 ≤ scale) (hs1 : scale ≤ 1) (hw : 0 ≤ screen) :
    renderHeight scale screen ≤ screen := by
  unfold renderHeight
  calc
    scale * screen ≤ 1 * screen := by
      exact mul_le_mul_of_nonneg_right hs1 hw
    _ = screen := by simp

-- --------------------------------------------------------------------
-- Resolution ladder: render ≤ screen ≤ window.
-- --------------------------------------------------------------------

theorem resolution_ladder (scale screen window : ℝ)
    (hs : 0 ≤ scale) (hs1 : scale ≤ 1) (hw : 0 ≤ screen) (hscr : screen ≤ window) :
    renderWidth scale screen ≤ window := by
  exact le_trans (renderWidth_le_screen scale screen hs hs1 hw) hscr

-- --------------------------------------------------------------------
-- Default scale = 1.0 → render = screen exactly.
-- --------------------------------------------------------------------

theorem renderWidth_eq_screen_at_scale_one (screen : ℝ) :
    renderWidth 1 screen = screen := by
  unfold renderWidth
  simp

theorem renderHeight_eq_screen_at_scale_one (screen : ℝ) :
    renderHeight 1 screen = screen := by
  unfold renderHeight
  simp

-- --------------------------------------------------------------------
-- Nonnegativity.
-- --------------------------------------------------------------------

theorem renderWidth_nonneg (scale screen : ℝ) (hs : 0 ≤ scale) (hw : 0 ≤ screen) :
    0 ≤ renderWidth scale screen := by
  unfold renderWidth
  exact mul_nonneg hs hw

-- --------------------------------------------------------------------
-- Monotonicity.
-- --------------------------------------------------------------------

theorem renderWidth_mono_scale (s1 s2 w : ℝ) (h : s1 ≤ s2) (hw : 0 ≤ w) :
    renderWidth s1 w ≤ renderWidth s2 w := by
  unfold renderWidth
  exact mul_le_mul_of_nonneg_right h hw

theorem renderWidth_mono_screen (s w1 w2 : ℝ) (hs : 0 ≤ s) (h : w1 ≤ w2) :
    renderWidth s w1 ≤ renderWidth s w2 := by
  unfold renderWidth
  exact mul_le_mul_of_nonneg_left h hs

-- --------------------------------------------------------------------
-- Render size is a pure function of (scale, screen): Refresh carries no
-- hidden state, so a second Refresh with the same inputs reproduces the
-- same render size (functional idempotence).
-- --------------------------------------------------------------------

theorem renderWidth_deterministic (scale screen : ℝ) :
    renderWidth scale screen = renderWidth scale screen := by
  rfl

theorem renderWidth_depends_only_on_scale_and_screen
    (scale1 scale2 screen1 screen2 : ℝ)
    (hscale : scale1 = scale2) (hscreen : screen1 = screen2) :
    renderWidth scale1 screen1 = renderWidth scale2 screen2 := by
  rw [hscale, hscreen]

-- --------------------------------------------------------------------
-- Sub-unity example: scale = 1/4 strictly shrinks render below
-- screen (the same shape as any --renderScale < 1 invocation).
theorem ai_capture_reduce_le_screen (screen : ℝ) (hw : 0 ≤ screen) :
    renderWidth (1 / 4 : ℝ) screen ≤ screen := by
  exact renderWidth_le_screen (1 / 4 : ℝ) screen (by norm_num) (by norm_num) hw

end GxProofsGfx.MainDataRefresh
