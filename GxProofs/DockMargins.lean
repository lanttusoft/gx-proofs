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
  gX — dock engage and cramped-fallback scale contract

  Models the current gX_GUI_Dock_Update and gX_GUI_Dock_Cramped_Check
  decisions in src/gui/gui.c. The left dock margin is 320px and the
  minimum viewport scale is 0.70. Initial engagement requires both width and
  height scales to reach that floor; a cramped check on an already docked
  window tests the width scale only. There is no separate 240px numeric
  fallback threshold in the current implementation.

  Pixel ratios are represented by cross-multiplied Nat inequalities. This is
  an exact-rational decision model, not a proof of F32 boundary rounding,
  monitor prediction, or the OS window transition.
-/

namespace GxProofs.DockMargins

def MARGIN : Nat := 320
def SCALE_MIN_NUM : Nat := 70
def SCALE_DEN : Nat := 100

def usableWidth (windowWidth rightInset : Nat) : Nat :=
  max 1 (windowWidth - MARGIN - rightInset)

def widthScaleOk (windowWidth rightInset screenWidth : Nat) : Bool :=
  decide (SCALE_MIN_NUM * screenWidth
    ≤ SCALE_DEN * usableWidth windowWidth rightInset)

def heightScaleOk (windowHeight screenHeight : Nat) : Bool :=
  decide (SCALE_MIN_NUM * screenHeight ≤ SCALE_DEN * windowHeight)

def engages (windowWidth windowHeight rightInset screenWidth screenHeight : Nat) : Bool :=
  widthScaleOk windowWidth rightInset screenWidth
    && heightScaleOk windowHeight screenHeight

def remainsDocked (windowWidth rightInset screenWidth : Nat) : Bool :=
  widthScaleOk windowWidth rightInset screenWidth

theorem margin_value : MARGIN = 320 := by
  decide

theorem scale_floor_value : SCALE_MIN_NUM * 1 = 70 := by
  decide

theorem engages_1080p_default : engages 1795 1011 380 1536 1152 = true := by
  decide

theorem too_narrow_rejects_engage : engages 1700 1011 380 1536 1152 = false := by
  decide

theorem too_short_rejects_engage : engages 1795 700 380 1536 1152 = false := by
  decide

theorem engage_requires_both_scales (ww wh inset sw sh : Nat)
    (h : engages ww wh inset sw sh = true) :
    widthScaleOk ww inset sw = true ∧ heightScaleOk wh sh = true := by
  simp [engages, Bool.and_eq_true] at h
  exact h

theorem cramped_fallback_is_width_only (ww inset sw : Nat) :
    remainsDocked ww inset sw = widthScaleOk ww inset sw := by
  rfl

theorem width_floor_keeps_dock (ww inset sw : Nat)
    (h : SCALE_MIN_NUM * sw ≤ SCALE_DEN * usableWidth ww inset) :
    remainsDocked ww inset sw = true := by
  simp [remainsDocked, widthScaleOk, h]

theorem below_width_floor_releases_dock (ww inset sw : Nat)
    (h : SCALE_DEN * usableWidth ww inset < SCALE_MIN_NUM * sw) :
    remainsDocked ww inset sw = false := by
  simp [remainsDocked, widthScaleOk]
  omega

end GxProofs.DockMargins
