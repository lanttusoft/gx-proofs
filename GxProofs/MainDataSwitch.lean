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
  gX — MainData Scene-Switch State Machine (kernel)

  Models the masterIndex switch/response handshake in
  src/main_update.c + src/scene/scene.c
  (gX_MainData_Switch + Update_After + Responses, re-verified):

    Switch(idx):            switch ← true,  switched ← false
    Update_After:
      if switched:          Responses()   [clears switched=false at end]
      if switch:            switched ← true, switch ← false

  States (switch, switched):
    idle     (false,false)  — no switch pending
    pending  (true,false)   — Switch called, awaiting consumption
    awaiting (false,true)   — switch consumed, responses pending
    done     (false,false)  — responses processed, back to idle

  Invariants:
    - the full Switch → Update → Update cycle returns to idle
    - at most one flag is set at a time in every reachable state
    - Switch is idempotent until consumed and clears any pending
      switched bit
    - masterIndexSuccessful requires all five responders
      (gui/input/renderer/scene/camera — always required, no gating)
-/


namespace GxProofs.MainDataSwitch

-- State is the pair (masterIndexSwitch, masterIndexSwitched).
abbrev SwitchState := Bool × Bool

-- gX_MainData_Switch: set switch, clear switched.
def doSwitch (_st : SwitchState) : SwitchState := (true, false)

-- gX_MainData_Update_After:
--   switch=true  → consume: switched=true, switch=false (awaiting response)
--   switch=false → nothing pending: (switched is cleared by Responses)
def step (st : SwitchState) : SwitchState :=
  match st with
  | (true, _)  => (false, true)
  | (false, _) => (false, false)

-- --------------------------------------------------------------------
-- Direct transitions.
-- --------------------------------------------------------------------

theorem switch_sets_flag : doSwitch (false, false) = (true, false) := by
  simp [doSwitch]

theorem pending_step_to_awaiting : step (true, false) = (false, true) := by
  simp [step]

theorem awaiting_step_to_done : step (false, true) = (false, false) := by
  simp [step]

theorem idle_stays_idle : step (false, false) = (false, false) := by
  simp [step]

-- --------------------------------------------------------------------
-- Full cycle: Switch → Update → Update returns to idle.
-- --------------------------------------------------------------------

theorem full_switch_cycle :
    step (step (doSwitch (false, false))) = (false, false) := by
  simp [doSwitch, step]

-- --------------------------------------------------------------------
-- Switch idempotence + it clears a pending switched bit.
-- --------------------------------------------------------------------

theorem switch_overrides_pending : doSwitch (true, false) = (true, false) := by
  simp [doSwitch]

theorem switch_clears_switched : doSwitch (false, true) = (true, false) := by
  simp [doSwitch]

theorem switch_then_step_awaiting : step (doSwitch (false, false)) = (false, true) := by
  simp [doSwitch, step]

-- --------------------------------------------------------------------
-- Reachable states never set both flags at once.
-- --------------------------------------------------------------------

theorem no_state_sets_both_flags :
    let s0 := (false, false)
    let s1 := doSwitch s0
    let s2 := step s1
    let s3 := step s2
    ¬ (s0.1 = true ∧ s0.2 = true) ∧
    ¬ (s1.1 = true ∧ s1.2 = true) ∧
    ¬ (s2.1 = true ∧ s2.2 = true) ∧
    ¬ (s3.1 = true ∧ s3.2 = true) := by
  simp [doSwitch, step]

-- --------------------------------------------------------------------
-- masterIndexSuccessful requires ALL FIVE responders in full builds
-- (gui, input, renderer, scene, AND camera are always checked in
-- gX_MainData_Responses, src/main_update.c). Kernel-only builds
-- compile the renderer/scene checks out (see #if guards) — the contract
-- below is the full-build half; the flag machine above holds in both.
-- Salvage surgery: the gameX original had 4 responders with
-- renderer/scene conditional on gX_ENABLE_*; gX always requires
-- all five, so the Enabled-gating and the two *_off theorems are
-- replaced by the camera theorem. They return with a kernel-only
-- build.
-- --------------------------------------------------------------------

structure Responded where
  gui      : Bool
  input    : Bool
  renderer : Bool
  scene    : Bool
  camera   : Bool

def allResponded (r : Responded) : Prop :=
  r.gui = true ∧ r.input = true ∧ r.renderer = true ∧
  r.scene = true ∧ r.camera = true

theorem success_requires_gui (r : Responded) (h : allResponded r) :
    r.gui = true :=
  h.1

theorem success_requires_input (r : Responded) (h : allResponded r) :
    r.input = true :=
  h.2.1

theorem success_requires_renderer (r : Responded) (h : allResponded r) :
    r.renderer = true :=
  h.2.2.1

theorem success_requires_scene (r : Responded) (h : allResponded r) :
    r.scene = true :=
  h.2.2.2.1

theorem success_requires_camera (r : Responded) (h : allResponded r) :
    r.camera = true :=
  h.2.2.2.2

end GxProofs.MainDataSwitch
