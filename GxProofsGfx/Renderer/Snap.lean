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
  gX — Grid-snap specification (Mathlib tier)

  Models tools_grid in src/tools/editor/editor.cpp: with snap
  on, coordinates round to the 8px grid (roundf(v/8)*8); with snap
  off, values pass through untouched. Snap gates drag-move and
  resize paths (tools_canvas_drag), so its contract bounds every
  snapped gesture.

  Proven here: snapping never moves a point more than 4px (half a
  cell — the "drag feels magnetic but never jumps" contract),
  snapping is idempotent (re-snapping a snapped value is a no-op, so
  repeated drag frames can't creep), and the toggle-off path is the
  identity.

  Theorems proven: 3
    - snap_within_4:  snapped values stay within half a cell
    - snap_idem:      snapping twice = snapping once (no creep)
    - grid_off:       snap-off passes values through
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

namespace GxProofsGfx.GridSnap

-- tools_grid with snap on: round to the 8px grid.
noncomputable def snap (v : ℝ) : ℝ := (round (v / 8) : ℝ) * 8

-- Toggle: snap on applies the grid, snap off is the identity.
noncomputable def grid (on : Bool) (v : ℝ) : ℝ :=
  if on then snap v else v

-- 1. Snapping moves a point at most half a cell (4px).
theorem snap_within_4 (v : ℝ) : |snap v - v| ≤ 4 := by
  unfold snap
  have h : |(round (v / 8) : ℝ) - v / 8| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round _
  have e : (round (v / 8) : ℝ) * 8 - v
      = 8 * ((round (v / 8) : ℝ) - v / 8) := by ring
  calc |(round (v / 8) : ℝ) * 8 - v|
      = 8 * |(round (v / 8) : ℝ) - v / 8| := by
        rw [e, abs_mul]
        norm_num
    _ ≤ 8 * (1 / 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 4 := by norm_num

-- 2. Idempotent: re-snapping is a no-op (no drag creep).
theorem snap_idem (v : ℝ) : snap (snap v) = snap v := by
  unfold snap
  have e : ((round (v / 8) : ℝ) * 8) / 8
      = (round (v / 8) : ℝ) := by field_simp
  rw [e, round_intCast]

-- 3. Snap-off is the identity.
theorem grid_off (v : ℝ) : grid false v = v :=
  rfl
