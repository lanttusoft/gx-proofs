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
  gX — GUI Grid Layout Bounds Specification
  8×8 grid from src/gui/builder.c:gX_GUI_Builder_RectGrid.
  Scope: the positive explicit-size Nat case (gx,gy,gw,gh ≥ 0).
  gX's RectGrid additionally supports float coords, negative-edge
  anchors, zero-fill, negative-shrink, and layout containers —
  those paths are unmodeled here, not contradicted.
  Elements with non-negative coords must satisfy x+w ≤ 8, y+h ≤ 8.
-/

--ai: finite layout examples use kernel reduction, not native compiler trust.
namespace GxProofs.GridLayout

def GRID : Nat := 8

structure Element where
  gx : Nat
  gy : Nat
  gw : Nat
  gh : Nat

def fits (e : Element) : Prop :=
  e.gx + e.gw ≤ GRID ∧ e.gy + e.gh ≤ GRID

theorem positive_coords_fit (e : Element) :
    e.gx + e.gw ≤ GRID → e.gy + e.gh ≤ GRID → fits e := by
  unfold fits; intro hx hy; exact And.intro hx hy

theorem right_anchored (gx gw : Nat) (h : gx + gw = GRID) : gx + gw ≤ GRID := by
  omega

theorem zero_width_fills (gx : Nat) (h : gx ≤ GRID) : gx + (GRID - gx) = GRID := by
  omega

theorem full_screen_fills : fits { gx := 0, gy := 0, gw := 8, gh := 8 } := by
  unfold fits; decide

theorem single_unit_fits : fits { gx := 0, gy := 0, gw := 1, gh := 1 } := by
  unfold fits; decide

theorem bottom_edge_fits : fits { gx := 0, gy := 7, gw := 8, gh := 1 } := by
  unfold fits; decide

theorem right_edge_fits : fits { gx := 7, gy := 0, gw := 1, gh := 8 } := by
  unfold fits; decide

end GxProofs.GridLayout
