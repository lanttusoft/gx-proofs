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
  //ai: exact label contracts grounded in billboard.c and gfx/draw.c.
  Raster padding assumes the final measured extent fits; the finite eight-step
  font-fitting loop, glyph overhang/atlas contents, UV routing and GPU execution
  are separate native/pixel obligations, not certified by these propositions.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace GxProofsGfx.LabelContracts

def quad (width height : ℚ) : ℚ × ℚ :=
  if 8 * height < width then (8 * height, height) else (width, width / 8)

theorem quad_preserves_aspect (width height : ℚ) :
    (quad width height).1 = 8 * (quad width height).2 := by
  unfold quad
  split_ifs
  · rfl
  · change width = 8 * (width / 8)
    ring

theorem quad_fits_box (width height : ℚ) (hw : 0 < width) (hh : 0 < height) :
    0 < (quad width height).1 ∧ 0 < (quad width height).2 ∧
    (quad width height).1 ≤ width ∧ (quad width height).2 ≤ height := by
  unfold quad
  split_ifs with h <;> constructor
  · linarith
  · constructor
    · exact hh
    · constructor <;> linarith
  · exact hw
  · constructor
    · positivity
    · constructor
      · rfl
      · linarith

def center (capacity extent : ℚ) : ℚ := (capacity - extent) / 2

theorem centered_extent (capacity extent : ℚ) :
    center capacity extent + extent / 2 = capacity / 2 := by
  unfold center
  ring

theorem raster_margin (capacity extent : ℚ) (h : extent ≤ capacity - 8) :
    4 ≤ center capacity extent := by
  unfold center
  linarith

theorem bounded_shadow_fits (capacity extent shadow : ℚ)
    (hf : extent ≤ capacity - 8)
    (hs : 0 ≤ shadow) (hu : shadow ≤ 4) :
    0 ≤ center capacity extent + shadow ∧
    center capacity extent + shadow + extent ≤ capacity := by
  unfold center
  constructor <;> linarith

theorem huge_font_counterexample : ¬ (256 : ℚ) ≤ 64 - 8 := by norm_num

--ai: this ideal homothetic witness is not the production spacing/remeasure loop.
def fitScale (width height availableWidth availableHeight : ℚ) : ℚ :=
  min (min 1 (availableWidth / width)) (availableHeight / height)

theorem ideal_scale_bounded (w h aw ah : ℚ) (hw : 0 < w) (hh : 0 < h)
    (haw : 0 ≤ aw) (hah : 0 ≤ ah) :
    0 ≤ fitScale w h aw ah ∧ fitScale w h aw ah ≤ 1 := by
  unfold fitScale
  constructor
  · exact le_min (le_min (by norm_num) (div_nonneg haw (le_of_lt hw)))
      (div_nonneg hah (le_of_lt hh))
  · exact le_trans (min_le_left _ _) (min_le_left _ _)

theorem ideal_scale_fits_width (w h aw ah : ℚ) (hw : 0 < w) :
    fitScale w h aw ah * w ≤ aw := by
  apply (le_div_iff₀ hw).mp
  exact le_trans (min_le_left _ _) (min_le_right _ _)

theorem ideal_scale_fits_height (w h aw ah : ℚ) (hh : 0 < h) :
    fitScale w h aw ah * h ≤ ah := by
  apply (le_div_iff₀ hh).mp
  exact min_le_right _ _

def topCenter (top gap height : ℚ) : ℚ := top + gap + height / 2

theorem label_lower_edge_gap (top gap height : ℚ) :
    topCenter top gap height - height / 2 = top + gap := by
  unfold topCenter
  ring

theorem label_above_bounds (corner top gap height : ℚ)
    (hc : corner ≤ top) (hg : 0 ≤ gap) :
    corner ≤ topCenter top gap height - height / 2 := by
  rw [label_lower_edge_gap]
  linarith

theorem top_anchor_follows_translation (top gap height delta : ℚ) :
    topCenter (top + delta) gap height = topCenter top gap height + delta := by
  unfold topCenter
  ring

theorem horizontal_center_follows_translation (low high delta : ℚ) :
    ((low + delta) + (high + delta)) / 2 = (low + high) / 2 + delta := by ring

theorem maximum_follows_translation (a b delta : ℚ) :
    max (a + delta) (b + delta) = max a b + delta := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

def flipV (v : ℚ) : ℚ := 1 - v

theorem uv_flip_involution (v : ℚ) : flipV (flipV v) = v := by
  unfold flipV
  ring

theorem uv_flip_range (v : ℚ) (hl : 0 ≤ v) (hu : v ≤ 1) :
    0 ≤ flipV v ∧ flipV v ≤ 1 := by
  unfold flipV
  constructor <;> linarith

theorem uv_top_bottom_swap : flipV 0 = 1 ∧ flipV 1 = 0 := by
  norm_num [flipV]

theorem normalized_byte_range (channel : ℚ) (hl : 0 ≤ channel) (hu : channel ≤ 255) :
    0 ≤ channel / 255 ∧ channel / 255 ≤ 1 := by constructor <;> linarith

end GxProofsGfx.LabelContracts
