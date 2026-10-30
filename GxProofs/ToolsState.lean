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
  gX — Tools Open/Close/Route State Machine

  Pins the runtime-tools state machine from
  src/tools/tools.c and src/gui/binding.c:
    - Exclusivity: opening any tool sets its flag and clears the
      other two (tools.c: OpenEditor/OpenTheme/OpenGfx_Runtime —
      one dock panel at a time).
    - Scene routing: the menu GFX button jumps to the GFX scene when
      opened from the title (binding.c: OnClick_OpenGfx — nothing to
      light on the title; mirrors --gfx-editor CLI routing), and stays
      put on scenes that already carry 3D content.
    - Close clears all three flags; the scene is untouched.

  Theorems proven: 7
    - open_gfx_exclusive:    gfx open ⇒ editor/theme closed
    - open_editor_exclusive: editor open ⇒ theme/gfx closed
    - open_theme_exclusive:  theme open ⇒ editor/gfx closed
    - open_gfx_routes:       title + open-gfx ⇒ GFX scene
    - open_gfx_stays:        3D scene + open-gfx ⇒ scene unchanged
    - close_clears_all:      close ⇒ all flags false
    - close_keeps_scene:     close ⇒ scene unchanged
-/

namespace GxProofs.ToolsState

-- The three dock tools.
inductive Tool where
  | editor
  | theme
  | gfx
deriving DecidableEq

-- Scenes relevant to routing: title, the GFX scene, anything else.
inductive Scene where
  | title
  | gfxScene
  | other
deriving DecidableEq

-- Full runtime state: per-tool flags + current scene.
structure State where
  editor : Bool
  theme : Bool
  gfx : Bool
  scene : Scene

-- Opening a tool (tools.c): set its flag, clear the other two.
def openTool (s : State) (t : Tool) : State :=
  match t with
  | .editor => { s with editor := true, theme := false, gfx := false }
  | .theme  => { s with editor := false, theme := true, gfx := false }
  | .gfx    => { s with editor := false, theme := false, gfx := true }

-- Menu GFX open (binding.c: OnClick_OpenGfx): route title → GFX scene,
-- then open exclusively.
def openGfxMenu (s : State) : State :=
  let routed :=
    match s.scene with
    | .title => { s with scene := .gfxScene }
    | _ => s
  openTool routed .gfx

-- Close (tools.c: Close_Runtime): all flags false, scene untouched.
def closeAll (s : State) : State :=
  { s with editor := false, theme := false, gfx := false }

-- Opening gfx is exclusive: editor and theme end closed, gfx open.
theorem open_gfx_exclusive (s : State) :
    let s' := openTool s .gfx
    s'.gfx = true ∧ s'.editor = false ∧ s'.theme = false := by
  simp [openTool]

-- Opening the GUI editor is exclusive.
theorem open_editor_exclusive (s : State) :
    let s' := openTool s .editor
    s'.editor = true ∧ s'.theme = false ∧ s'.gfx = false := by
  simp [openTool]

-- Opening the theme editor is exclusive.
theorem open_theme_exclusive (s : State) :
    let s' := openTool s .theme
    s'.theme = true ∧ s'.editor = false ∧ s'.gfx = false := by
  simp [openTool]

-- Menu GFX open from the title routes to the GFX scene (and is exclusive).
theorem open_gfx_routes (s : State) (h : s.scene = .title) :
    let s' := openGfxMenu s
    s'.scene = .gfxScene ∧ s'.gfx = true ∧ s'.editor = false ∧ s'.theme = false := by
  simp [openGfxMenu, openTool, h]

-- Menu GFX open off-title leaves the scene alone (still exclusive).
theorem open_gfx_stays (s : State) (h : s.scene ≠ .title) :
    (openGfxMenu s).scene = s.scene ∧ (openGfxMenu s).gfx = true := by
  cases hs : s.scene with
  | title => exact absurd hs h
  | gfxScene => simp [openGfxMenu, openTool, hs]
  | other => simp [openGfxMenu, openTool, hs]

-- Close clears every flag.
theorem close_clears_all (s : State) :
    let s' := closeAll s
    s'.editor = false ∧ s'.theme = false ∧ s'.gfx = false := by
  simp [closeAll]

-- Close never touches the scene.
theorem close_keeps_scene (s : State) :
    (closeAll s).scene = s.scene := by
  simp [closeAll]

end GxProofs.ToolsState
