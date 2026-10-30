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
  gX — Title Yields to Themlab

  Pins the gallery-takes-over protocol from
  src/gui/templates/titlegx.c (gX_GUI_Template_TitleGX): when
  canvas 2 carries the themlab template, the title draws nothing — the
  gallery's opaque full-canvas backdrop intends to replace the scene,
  and compositing both interleaves two full UIs. Canvas-2 presence is
  the signal, so every close path restores the title automatically.

  Theorems proven: 4
    - lab_up_hides_title:   themlab on canvas 2 → title skipped
    - lab_down_shows_title: other canvas-2 content → title drawn
    - close_restores_title: removing the lab canvas → title drawn
    - title_exclusive:      title is drawn iff the lab is not up
-/

namespace GxProofs.TitleYield

-- Template IDs (only the two that matter here).
inductive Template where
  | title
  | themlab
  | other
deriving DecidableEq

-- Title draws iff canvas 2 does NOT carry the themlab template.
def titleDrawn (canvas2 : Option Template) : Bool :=
  match canvas2 with
  | some .themlab => false
  | _ => true

-- Themlab on canvas 2 → title skipped.
theorem lab_up_hides_title :
    titleDrawn (some .themlab) = false := rfl

-- Any other canvas-2 content → title drawn.
theorem lab_down_shows_title (t : Template) (h : t ≠ .themlab) :
    titleDrawn (some t) = true := by
  cases t with
  | themlab => exact absurd rfl h
  | title => rfl
  | other => rfl

-- Removing the lab canvas (close path) → title drawn.
theorem close_restores_title :
    titleDrawn none = true := rfl

-- Exclusivity: title is drawn exactly when the lab is not up.
theorem title_exclusive (canvas2 : Option Template) :
    titleDrawn canvas2 = !(canvas2 = some .themlab) := by
  cases canvas2 with
  | none => rfl
  | some t =>
    cases t <;> rfl

end GxProofs.TitleYield
