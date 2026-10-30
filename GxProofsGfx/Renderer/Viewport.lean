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
  gX — Docked viewport scale specification (Mathlib tier)

  Models the docked branch of gX_GUI_Viewport_Refresh in
  src/gui/gui.c: usable width is max(1, windowWidth - 320 - rightInset),
  scale is limited by width and height, then clamped to [0.70, 1]. The viewport
  starts at x=320 and is vertically centered.

  The fit theorems are conditional: the 0.70 minimum can exceed a too-small
  width or height. In particular, after a short user resize the dock-cramp
  check only tests width; a height overflow may exist for the intervening
  refresh. This exact-real model does not prove float evaluation, the OS resize
  event, or render-target allocation/pool behavior.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.ViewportFit

def dockMargin : ℝ := 320
noncomputable def dockScaleFloor : ℝ := (7 : ℝ) / 10

noncomputable def usableWidth (ww rightInset : ℝ) : ℝ := max 1 (ww - dockMargin - rightInset)
noncomputable def widthScale (gw ww rightInset : ℝ) : ℝ := usableWidth ww rightInset / gw
noncomputable def heightScale (gh wh : ℝ) : ℝ := wh / gh

noncomputable def dockScale (gw gh ww wh rightInset : ℝ) : ℝ :=
  min 1 (max dockScaleFloor (min (widthScale gw ww rightInset)
    (heightScale gh wh)))

noncomputable def viewportWidth (gw gh ww wh rightInset : ℝ) : ℝ :=
  gw * dockScale gw gh ww wh rightInset

noncomputable def viewportHeight (gw gh ww wh rightInset : ℝ) : ℝ :=
  gh * dockScale gw gh ww wh rightInset

noncomputable def viewportY (gw gh ww wh rightInset : ℝ) : ℝ :=
  (wh - viewportHeight gw gh ww wh rightInset) / 2

theorem dock_margin_value : dockMargin = 320 := by
  norm_num [dockMargin]

theorem dock_scale_floor_value : dockScaleFloor = 0.70 := by
  norm_num [dockScaleFloor]

theorem dockScale_le_one (gw gh ww wh rightInset : ℝ) :
    dockScale gw gh ww wh rightInset ≤ 1 := by
  exact min_le_left _ _

theorem dockScale_ge_floor (gw gh ww wh rightInset : ℝ) :
    dockScaleFloor ≤ dockScale gw gh ww wh rightInset := by
  have hfloor : dockScaleFloor ≤ 1 := by norm_num [dockScaleFloor]
  have hmax : dockScaleFloor ≤ max dockScaleFloor
      (min (widthScale gw ww rightInset) (heightScale gh wh)) := le_max_left _ _
  exact le_min hfloor hmax

theorem dockScale_le_widthScale (gw gh ww wh rightInset : ℝ)
    (hfloor : dockScaleFloor ≤ widthScale gw ww rightInset) :
    dockScale gw gh ww wh rightInset ≤ widthScale gw ww rightInset := by
  have hcandidate : min (widthScale gw ww rightInset) (heightScale gh wh)
      ≤ widthScale gw ww rightInset := min_le_left _ _
  have hclamped : max dockScaleFloor
      (min (widthScale gw ww rightInset) (heightScale gh wh))
      ≤ widthScale gw ww rightInset := max_le hfloor hcandidate
  exact le_trans (min_le_right _ _) hclamped

theorem dockScale_le_heightScale (gw gh ww wh rightInset : ℝ)
    (hfloor : dockScaleFloor ≤ heightScale gh wh) :
    dockScale gw gh ww wh rightInset ≤ heightScale gh wh := by
  have hcandidate : min (widthScale gw ww rightInset) (heightScale gh wh)
      ≤ heightScale gh wh := min_le_right _ _
  have hclamped : max dockScaleFloor
      (min (widthScale gw ww rightInset) (heightScale gh wh))
      ≤ heightScale gh wh := max_le hfloor hcandidate
  exact le_trans (min_le_right _ _) hclamped

theorem docked_width_fits (gw gh ww wh rightInset : ℝ)
    (hgw : 0 < gw)
    (hraw : 1 ≤ ww - dockMargin - rightInset)
    (hfloor : gw * dockScaleFloor ≤ ww - dockMargin - rightInset) :
    dockMargin + rightInset + viewportWidth gw gh ww wh rightInset ≤ ww := by
  have husable : usableWidth ww rightInset = ww - dockMargin - rightInset := by
    unfold usableWidth
    exact max_eq_right hraw
  have hfloorScale : dockScaleFloor ≤ widthScale gw ww rightInset := by
    unfold widthScale
    rw [husable]
    apply (le_div_iff₀ hgw).2
    nlinarith [hfloor]
  have hscale := dockScale_le_widthScale gw gh ww wh rightInset hfloorScale
  have hwidth : gw * dockScale gw gh ww wh rightInset
      ≤ ww - dockMargin - rightInset := by
    have hmul : dockScale gw gh ww wh rightInset * gw
        ≤ ww - dockMargin - rightInset := by
      apply (le_div_iff₀ hgw).1
      simpa [widthScale, husable] using hscale
    nlinarith [hmul]
  unfold viewportWidth
  linarith

theorem docked_height_fits (gw gh ww wh rightInset : ℝ)
    (hgh : 0 < gh)
    (hfloor : gh * dockScaleFloor ≤ wh) :
    viewportHeight gw gh ww wh rightInset ≤ wh := by
  have hfloorScale : dockScaleFloor ≤ heightScale gh wh := by
    unfold heightScale
    apply (le_div_iff₀ hgh).2
    nlinarith [hfloor]
  have hscale := dockScale_le_heightScale gw gh ww wh rightInset hfloorScale
  have hheight : gh * dockScale gw gh ww wh rightInset ≤ wh := by
    have hmul : dockScale gw gh ww wh rightInset * gh ≤ wh := by
      apply (le_div_iff₀ hgh).1
      simpa [heightScale] using hscale
    nlinarith [hmul]
  exact hheight

theorem centered_y_nonnegative (gw gh ww wh rightInset : ℝ)
    (hfit : viewportHeight gw gh ww wh rightInset ≤ wh) :
    0 ≤ viewportY gw gh ww wh rightInset := by
  unfold viewportY
  linarith

theorem minimum_scale_can_overflow_height :
    viewportHeight 100 100 2000 60 0 > 60 := by
  norm_num [viewportHeight, dockScale, dockScaleFloor, widthScale,
    heightScale, usableWidth, dockMargin]

end GxProofsGfx.ViewportFit
