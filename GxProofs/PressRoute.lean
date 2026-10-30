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
  gX — Editor press-routing specification

  Models the gesture-ownership decision from
  src/tools/editor/editor.cpp:tools_canvas_drag: a press starts
  a canvas gesture iff it was NOT captured by ImGui AND it landed
  inside the viewport. Captured presses latch (s_pressCaptured) until
  release, so gestures born on ImGui never reach the canvas while a
  canvas-owned gesture survives panel crossing mid-drag.

  Proven here is the routing partition both halves rely on: the two
  reject classes (ImGui-born, pillarbox-void) can never start a
  gesture, and a started gesture is always a non-captured in-viewport
  press. Any future double-select / missed-press report must therefore
  live in the inputs (WantCaptureMouse, viewport box), not the branch.

  Theorems proven: 4
    - captured_never:   ImGui-born presses never start gestures
    - void_never:       out-of-viewport presses never start gestures
    - canvas_gesture:   gestures are exactly non-captured in-viewport
    - gesture_in_view:  a started gesture is always in-viewport
-/

namespace GxProofs.PressRoute

-- Gesture-start decision: not captured, inside viewport.
def gestureStarts (captured inViewport : Bool) : Bool :=
  !captured && inViewport

-- 1. Presses born on ImGui never start a canvas gesture (no
-- panel-click select/deselect), whatever the viewport says.
theorem captured_never (v : Bool) : gestureStarts true v = false := by
  cases v <;> rfl

-- 2. Presses in the pillarbox void are ignored outright.
theorem void_never (c : Bool) : gestureStarts c false = false := by
  cases c <;> rfl

-- 3. Exact characterization: gestures are non-captured in-viewport
-- presses, nothing else.
theorem canvas_gesture (c v : Bool) :
    gestureStarts c v = true ↔ c = false ∧ v = true := by
  cases c <;> cases v <;> simp [gestureStarts]

-- 4. Projection: a started gesture is always in-viewport (the
-- viewport-reject branch is total).
theorem gesture_in_view (c v : Bool) (h : gestureStarts c v = true) :
    v = true := by
  cases c <;> cases v <;> simp_all [gestureStarts]
