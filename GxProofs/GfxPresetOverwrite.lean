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
  //ai: finite state machine for user-initiated GFX preset overwrite confirmation.

  Models gfx_preset_save and the overwrite modal in
  src/tools/gfx/gfx_editor.cpp. A nonempty path to an existing file
  raises a pending prompt; the panel opens the dialog; only an explicit
  confirmation requests a save commit. Cancel closes the dialog without a
  commit. A path to a new file follows the existing direct-save path.

  commitAttempts counts calls authorized to enter gfx_preset_save_commit, not
  successful disk writes. File I/O, JSON serialization, modal input delivery,
  and ImGui frame behavior remain outside the model. This models each save
  request as one transaction; it makes no claim about overlapping shortcut,
  popup, or programmatic requests.
-/

namespace GxProofs.GfxPresetOverwrite

inductive Phase where
  | idle
  | confirmationPending
  | dialogOpen
  | cancelled
  | commitAttempted
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  commitAttempts : Nat
  deriving DecidableEq, Repr

def initial : State := ⟨.idle, 0⟩

def requestSave (state : State) (hasPath targetExists : Bool) : State :=
  if hasPath then
    if targetExists then { state with phase := .confirmationPending }
    else { state with
      phase := .commitAttempted
      commitAttempts := state.commitAttempts + 1
    }
  else state

def showOverwriteDialog (state : State) : State :=
  if state.phase = .confirmationPending then { state with phase := .dialogOpen }
  else state

def confirmOverwrite (state : State) : State :=
  if state.phase = .dialogOpen then { state with
    phase := .commitAttempted
    commitAttempts := state.commitAttempts + 1
  } else state

def cancelOverwrite (state : State) : State :=
  if state.phase = .dialogOpen then { state with phase := .cancelled }
  else state

theorem empty_path_does_not_attempt_save (state : State) (targetExists : Bool) :
    requestSave state false targetExists = state := by
  cases state.phase <;> simp [requestSave]

theorem new_path_attempts_save_directly (attempts : Nat) :
    requestSave ⟨.idle, attempts⟩ true false = ⟨.commitAttempted, attempts + 1⟩ := by
  simp [requestSave]

theorem existing_path_only_requests_confirmation (attempts : Nat) :
    requestSave ⟨.idle, attempts⟩ true true =
      ⟨.confirmationPending, attempts⟩ := by
  simp [requestSave]

theorem pending_opens_dialog_without_commit (attempts : Nat) :
    showOverwriteDialog (requestSave ⟨.idle, attempts⟩ true true) =
      ⟨.dialogOpen, attempts⟩ := by
  simp [requestSave, showOverwriteDialog]

theorem cancel_preserves_attempt_count (attempts : Nat) :
    cancelOverwrite
      (showOverwriteDialog (requestSave ⟨.idle, attempts⟩ true true)) =
        ⟨.cancelled, attempts⟩ := by
  simp [requestSave, showOverwriteDialog, cancelOverwrite]

theorem confirm_requests_exactly_one_commit (attempts : Nat) :
    confirmOverwrite
      (showOverwriteDialog (requestSave ⟨.idle, attempts⟩ true true)) =
        ⟨.commitAttempted, attempts + 1⟩ := by
  simp [requestSave, showOverwriteDialog, confirmOverwrite]

theorem second_confirm_does_not_repeat_commit (state : State)
    (openDialog : state.phase = .dialogOpen) :
    (confirmOverwrite (confirmOverwrite state)).commitAttempts =
      state.commitAttempts + 1 := by
  simp [confirmOverwrite, openDialog]

theorem confirm_outside_dialog_is_noop (state : State)
    (notOpen : state.phase ≠ .dialogOpen) :
    confirmOverwrite state = state := by
  simp [confirmOverwrite, notOpen]

theorem cancel_outside_dialog_is_noop (state : State)
    (notOpen : state.phase ≠ .dialogOpen) :
    cancelOverwrite state = state := by
  simp [cancelOverwrite, notOpen]

end GxProofs.GfxPresetOverwrite
