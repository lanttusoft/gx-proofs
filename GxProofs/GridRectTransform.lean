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
  gX — GUI Grid-to-Pixel Rect Transform Specification
  Models the positive explicit-size case of RectGrid from
  src/gui/builder.c:gX_GUI_Builder_RectGrid (Nat grid units
  scaled by widthDiv/heightDiv stay in-screen). Negative anchors,
  fill, and container-relative paths are unmodeled, not contradicted.
  Proves that valid grid coords map to valid pixel-space rects.
-/

import GxProofs.GridLayout

--ai: divisibility witnesses use kernel reduction rather than native compiler trust.
namespace GxProofs.GridRectTransform

structure GridCoord where
  gx : Nat
  gy : Nat
  gw : Nat
  gh : Nat

structure PixelRect where
  ex : Nat
  ey : Nat
  ew : Nat
  eh : Nat

structure Screen where
  w   : Nat
  h   : Nat
  wDiv : Nat
  hDiv : Nat
  h8w : 8 * wDiv ≤ w
  h8h : 8 * hDiv ≤ h

def rectGridPos (s : Screen) (gc : GridCoord) : PixelRect :=
  { ex := gc.gx * s.wDiv,
    ey := gc.gy * s.hDiv,
    ew := gc.gw * s.wDiv,
    eh := gc.gh * s.hDiv }

-- =============================================================
-- Cases 1a/1b: positive anchor, explicit size
-- =============================================================

theorem pos_left_explicit_w (s : Screen) (gc : GridCoord)
    (h_fits : GridLayout.fits { gx := gc.gx, gy := gc.gy, gw := gc.gw, gh := gc.gh }) :
    (rectGridPos s gc).ex + (rectGridPos s gc).ew ≤ s.w := by
  rcases h_fits with ⟨hxw, hyh⟩
  calc
    (rectGridPos s gc).ex + (rectGridPos s gc).ew = gc.gx * s.wDiv + gc.gw * s.wDiv := rfl
    _ = (gc.gx + gc.gw) * s.wDiv := by rw [← Nat.add_mul]
    _ ≤ 8 * s.wDiv := Nat.mul_le_mul hxw (Nat.le_refl s.wDiv)
    _ ≤ s.w := s.h8w

theorem pos_top_explicit_h (s : Screen) (gc : GridCoord)
    (h_fits : GridLayout.fits { gx := gc.gx, gy := gc.gy, gw := gc.gw, gh := gc.gh }) :
    (rectGridPos s gc).ey + (rectGridPos s gc).eh ≤ s.h := by
  rcases h_fits with ⟨hxw, hyh⟩
  calc
    (rectGridPos s gc).ey + (rectGridPos s gc).eh = gc.gy * s.hDiv + gc.gh * s.hDiv := rfl
    _ = (gc.gy + gc.gh) * s.hDiv := by rw [← Nat.add_mul]
    _ ≤ 8 * s.hDiv := Nat.mul_le_mul hyh (Nat.le_refl s.hDiv)
    _ ≤ s.h := s.h8h

-- =============================================================
-- Cases 4a/4b: negative anchor, explicit size
-- NegXCoord: anchored from right edge.
-- ex = (8 - rightDist) * wDiv.  Must satisfy gw ≤ rightDist
-- (otherwise the element extends past the left edge).
-- =============================================================

structure NegXCoord where
  rightDist : Nat
  gw        : Nat
  h_right   : rightDist ≤ 8
  h_gw_le   : gw ≤ rightDist

def rectGridNegX (s : Screen) (nx : NegXCoord) : PixelRect :=
  { ex := (8 - nx.rightDist) * s.wDiv,
    ey := 0,
    ew := nx.gw * s.wDiv,
    eh := 0 }

theorem neg_right_explicit_w (s : Screen) (nx : NegXCoord) :
    (rectGridNegX s nx).ex + (rectGridNegX s nx).ew ≤ s.w := by
  have h_sub_add : (8 - nx.rightDist) + nx.rightDist = 8 :=
    Nat.sub_add_cancel nx.h_right
  have h_sum : (8 - nx.rightDist) + nx.gw ≤ 8 := by
    calc
      (8 - nx.rightDist) + nx.gw ≤ (8 - nx.rightDist) + nx.rightDist :=
        Nat.add_le_add_left nx.h_gw_le (8 - nx.rightDist)
      _ = 8 := h_sub_add
  calc
    (rectGridNegX s nx).ex + (rectGridNegX s nx).ew
        = (8 - nx.rightDist) * s.wDiv + nx.gw * s.wDiv := rfl
    _ = ((8 - nx.rightDist) + nx.gw) * s.wDiv := by rw [← Nat.add_mul]
    _ ≤ 8 * s.wDiv := Nat.mul_le_mul h_sum (Nat.le_refl s.wDiv)
    _ ≤ s.w := s.h8w

structure NegYCoord where
  bottomDist : Nat
  gh         : Nat
  h_bottom   : bottomDist ≤ 8
  h_gh_le    : gh ≤ bottomDist

def rectGridNegY (s : Screen) (ny : NegYCoord) : PixelRect :=
  { ex := 0,
    ey := (8 - ny.bottomDist) * s.hDiv,
    ew := 0,
    eh := ny.gh * s.hDiv }

theorem neg_bottom_explicit_h (s : Screen) (ny : NegYCoord) :
    (rectGridNegY s ny).ey + (rectGridNegY s ny).eh ≤ s.h := by
  have h_sub_add : (8 - ny.bottomDist) + ny.bottomDist = 8 :=
    Nat.sub_add_cancel ny.h_bottom
  have h_sum : (8 - ny.bottomDist) + ny.gh ≤ 8 := by
    calc
      (8 - ny.bottomDist) + ny.gh ≤ (8 - ny.bottomDist) + ny.bottomDist :=
        Nat.add_le_add_left ny.h_gh_le (8 - ny.bottomDist)
      _ = 8 := h_sub_add
  calc
    (rectGridNegY s ny).ey + (rectGridNegY s ny).eh
        = (8 - ny.bottomDist) * s.hDiv + ny.gh * s.hDiv := rfl
    _ = ((8 - ny.bottomDist) + ny.gh) * s.hDiv := by rw [← Nat.add_mul]
    _ ≤ 8 * s.hDiv := Nat.mul_le_mul h_sum (Nat.le_refl s.hDiv)
    _ ≤ s.h := s.h8h

-- =============================================================
-- Cases 2a/2b: positive anchor, zero size = fill remaining
-- =============================================================

def rectGridFillW (s : Screen) (gx : Nat) (_h : gx ≤ 8) : PixelRect :=
  { ex := gx * s.wDiv,
    ey := 0,
    ew := (8 - gx) * s.wDiv,
    eh := 0 }

theorem pos_left_fill_w (s : Screen) (gx : Nat) (h : gx ≤ 8) :
    (rectGridFillW s gx h).ex + (rectGridFillW s gx h).ew = 8 * s.wDiv := by
  have h_sub : gx + (8 - gx) = 8 := by omega
  calc
    (rectGridFillW s gx h).ex + (rectGridFillW s gx h).ew
        = gx * s.wDiv + (8 - gx) * s.wDiv := rfl
    _ = (gx + (8 - gx)) * s.wDiv := by rw [← Nat.add_mul]
    _ = 8 * s.wDiv := congrArg (fun x : Nat => x * s.wDiv) h_sub

def rectGridFillH (s : Screen) (gy : Nat) (_h : gy ≤ 8) : PixelRect :=
  { ex := 0,
    ey := gy * s.hDiv,
    ew := 0,
    eh := (8 - gy) * s.hDiv }

theorem pos_top_fill_h (s : Screen) (gy : Nat) (h : gy ≤ 8) :
    (rectGridFillH s gy h).ey + (rectGridFillH s gy h).eh = 8 * s.hDiv := by
  have h_sub : gy + (8 - gy) = 8 := by omega
  calc
    (rectGridFillH s gy h).ey + (rectGridFillH s gy h).eh
        = gy * s.hDiv + (8 - gy) * s.hDiv := rfl
    _ = (gy + (8 - gy)) * s.hDiv := by rw [← Nat.add_mul]
    _ = 8 * s.hDiv := congrArg (fun x : Nat => x * s.hDiv) h_sub

-- =============================================================
-- Concrete examples at 1024x768
-- =============================================================

def screen1024x768 : Screen :=
  { w := 1024, h := 768, wDiv := 128, hDiv := 96,
    h8w := by decide, h8h := by decide }

theorem full_screen :
    (rectGridPos screen1024x768 { gx := 0, gy := 0, gw := 8, gh := 8 })
    = { ex := 0, ey := 0, ew := 1024, eh := 768 } := by
  unfold rectGridPos screen1024x768; simp

theorem half_width :
    (rectGridPos screen1024x768 { gx := 0, gy := 0, gw := 4, gh := 8 }).ew = 512 := by
  unfold rectGridPos screen1024x768; simp

theorem bottom_row :
    (rectGridPos screen1024x768 { gx := 0, gy := 7, gw := 8, gh := 1 })
    = { ex := 0, ey := 672, ew := 1024, eh := 96 } := by
  unfold rectGridPos screen1024x768; simp

-- =============================================================
-- Truncation error: widthDiv = floor(screenW/8), error < 8px
-- =============================================================

theorem truncation_error_bounded (screenW : Nat) :
    let wDiv := screenW / 8
    8 * wDiv ≤ screenW ∧ screenW - 8 * wDiv < 8 := by
  intro wDiv
  have h_lt : screenW % 8 < 8 := Nat.mod_lt screenW (by omega : 0 < 8)
  have h_eq : screenW = 8 * (screenW / 8) + screenW % 8 := (Nat.div_add_mod screenW 8).symm
  constructor
  · exact Nat.mul_div_le screenW 8
  · omega

end GxProofs.GridRectTransform
