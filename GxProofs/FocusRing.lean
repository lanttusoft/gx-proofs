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
  gX — Focus Ring Geometry

  Pins the keyboard-focus ring from
  src/gui/element/element.c:449-463: the ring is the element
  rect grown by the style offset on all four sides
    (focusRect.x/y −= offset; width/height += 2·offset),
  with default offset gX_GUI_FOCUS_RING_OFFSET = 3.0 (gui/config.h:167).

  Pixel geometry modeled over Nat (floor of the F32 rects).

  Theorems proven: 6
    - ring_contains_left:    ring.x ≤ rect.x
    - ring_contains_top:     ring.y ≤ rect.y
    - ring_extends_right:    rect right edge ≤ ring right edge
    - ring_extends_bottom:   rect bottom edge ≤ ring bottom edge
    - ring_dims:             ring is exactly 2·offset wider/taller
    - default_offset_three:  the default ring grows rects by 3px/side
-/

namespace GxProofs.FocusRing

structure Rect where
  x : Nat
  y : Nat
  w : Nat
  h : Nat

-- Focus ring (element.c:453-458): grow by offset on every side.
def ring (r : Rect) (offset : Nat) : Rect :=
  { x := r.x - offset, y := r.y - offset
  , w := r.w + 2 * offset, h := r.h + 2 * offset }

-- The ring never starts right of / below the element origin.
theorem ring_contains_left (r : Rect) (o : Nat) :
    (ring r o).x ≤ r.x := by
  simp [ring]

theorem ring_contains_top (r : Rect) (o : Nat) :
    (ring r o).y ≤ r.y := by
  simp [ring]

-- The ring's right edge reaches at least the element's right edge.
theorem ring_extends_right (r : Rect) (o : Nat) (h : o ≤ r.x) :
    r.x + r.w ≤ (ring r o).x + (ring r o).w := by
  unfold ring; simp
  omega

-- The ring's bottom edge reaches at least the element's bottom edge.
theorem ring_extends_bottom (r : Rect) (o : Nat) (h : o ≤ r.y) :
    r.y + r.h ≤ (ring r o).y + (ring r o).h := by
  unfold ring; simp
  omega

-- The ring is exactly 2·offset wider and taller than the element.
theorem ring_dims (r : Rect) (o : Nat) :
    (ring r o).w = r.w + 2 * o ∧ (ring r o).h = r.h + 2 * o := by
  unfold ring; simp

-- Default offset 3 (gui/config.h:167): ring grows every side by 3.
theorem default_offset_three (r : Rect) :
    (ring r 3).w = r.w + 6 ∧ (ring r 3).h = r.h + 6 := by
  simp [ring]

end GxProofs.FocusRing
