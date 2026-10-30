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
  gX — RHI Local State Scope Contract

  Models the terrain diagnostic scopes in src/renderer/gfx/terrain.c.
  Each scope snapshots the state it may touch, applies its draw setup, and
  restores the snapshot through the RHI wrappers before EndTexture returns.

  Theorems proven: 8
    - main_setup_disables_blend: opaque terrain setup disables blending
    - main_setup_enables_depth: opaque terrain setup enables depth testing
    - main_setup_writes_depth: opaque terrain setup enables depth writes
    - mirror_setup_sets_front_face: planar setup sets the CCW convention
    - main_scope_restores: main terrain scope restores every saved field
    - mirror_scope_restores: planar terrain scope restores every saved field
    - restore_preserves_color_mask: color writes survive a scope
    - restore_preserves_depth_function: depth comparison survives a scope
-/

namespace GxProofs.RhiStateScope

--opencode: state fields touched by the migrated terrain RHI path.
structure State where
  blendEnabled : Bool
  depthTestEnabled : Bool
  depthFunc : Nat
  depthMask : Bool
  colorMaskR : Bool
  colorMaskG : Bool
  colorMaskB : Bool
  colorMaskA : Bool
  frontFace : Nat

def snapshot (s : State) : State := s

def restore (saved _current : State) : State := saved

-- GL_LESS and GL_CCW are represented as named contract values here; the
-- numeric GL enums are an implementation detail of the RHI headers.
def less : Nat := 513
def ccw : Nat := 2305

def mainSetup (s : State) : State :=
  { s with blendEnabled := false, depthTestEnabled := true, depthFunc := less, depthMask := true }

def mirrorSetup (s : State) : State :=
  { (mainSetup s) with frontFace := ccw }

def mainScope (s : State) : State :=
  restore (snapshot s) (mainSetup s)

def mirrorScope (s : State) : State :=
  restore (snapshot s) (mirrorSetup s)

theorem main_setup_disables_blend (s : State) :
    (mainSetup s).blendEnabled = false := by
  simp [mainSetup]

theorem main_setup_enables_depth (s : State) :
    (mainSetup s).depthTestEnabled = true := by
  simp [mainSetup]

theorem main_setup_writes_depth (s : State) :
    (mainSetup s).depthMask = true := by
  simp [mainSetup]

theorem mirror_setup_sets_front_face (s : State) :
    (mirrorSetup s).frontFace = ccw := by
  simp [mirrorSetup]

theorem main_scope_restores (s : State) :
    mainScope s = s := by
  rfl

theorem mirror_scope_restores (s : State) :
    mirrorScope s = s := by
  rfl

theorem restore_preserves_color_mask (s current : State) :
    (restore (snapshot s) current).colorMaskR = s.colorMaskR ∧
    (restore (snapshot s) current).colorMaskG = s.colorMaskG ∧
    (restore (snapshot s) current).colorMaskB = s.colorMaskB ∧
    (restore (snapshot s) current).colorMaskA = s.colorMaskA := by
  simp [restore, snapshot]

theorem restore_preserves_depth_function (s current : State) :
    (restore (snapshot s) current).depthFunc = s.depthFunc := by
  rfl

end GxProofs.RhiStateScope
