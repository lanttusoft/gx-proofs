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
  //ai: finite transition model for accepted/rejected client-window resize sync.

  Models gX_GUI_WindowResize_Sync and its three window-sized render targets in
  src/gui/gui.c. Inputs at or below the strict 320x240 thresholds, and
  repeated dimensions, are no-ops. An accepted resize updates the client size,
  preserves the logical game resolution, requests a viewport refresh, and marks
  ping/pong/composite targets for reload at the new size.

  viewportRefreshes is a ghost trace count, not an engine field. The model does
  not prove WM event delivery, float viewport geometry, buffer-pool behavior,
  successful GPU allocation, or GL rendering.
-/

import Mathlib.Tactic

namespace GxProofsGfx.Kernel.WindowResize

structure Size where
  width : Int
  height : Int
  deriving DecidableEq, Repr

structure Target where
  size : Size
  loaded : Bool
  loadPending : Bool
  deriving DecidableEq, Repr

structure State where
  window : Size
  screen : Size
  ping : Target
  pong : Target
  compositeBackground : Target
  viewportRefreshes : Nat
  deriving DecidableEq, Repr

structure Result where
  state : State
  changed : Bool
  deriving DecidableEq, Repr

def validLiveSize (live : Size) : Bool :=
  decide (320 < live.width ∧ 240 < live.height)

def resizedTarget (size : Size) : Target :=
  ⟨size, false, true⟩

def sync (state : State) (live : Size) : Result :=
  if validLiveSize live then
    if state.window = live then ⟨state, false⟩
    else ⟨{ state with
      window := live
      ping := resizedTarget live
      pong := resizedTarget live
      compositeBackground := resizedTarget live
      viewportRefreshes := state.viewportRefreshes + 1
    }, true⟩
  else ⟨state, false⟩

theorem rejected_resize_preserves_state (state : State) (live : Size)
    (rejected : validLiveSize live = false) :
    (sync state live).state = state ∧ (sync state live).changed = false := by
  simp [sync, rejected]

theorem same_size_is_noop (state : State) (live : Size)
    (valid : validLiveSize live = true) (same : state.window = live) :
    (sync state live).state = state ∧ (sync state live).changed = false := by
  simp [sync, valid, same]

theorem accepted_resize_updates_window_targets (state : State) (live : Size)
    (valid : validLiveSize live = true) (different : state.window ≠ live) :
    let next := (sync state live).state
    (sync state live).changed = true ∧
    next.window = live ∧
    next.screen = state.screen ∧
    next.ping = resizedTarget live ∧
    next.pong = resizedTarget live ∧
    next.compositeBackground = resizedTarget live ∧
    next.viewportRefreshes = state.viewportRefreshes + 1 := by
  simp [sync, valid, different]

theorem valid_threshold_edges :
    validLiveSize ⟨320, 241⟩ = false ∧
    validLiveSize ⟨321, 240⟩ = false ∧
    validLiveSize ⟨321, 241⟩ = true := by
  decide

theorem accepted_resize_then_repeat_is_noop (state : State) (live : Size)
    (valid : validLiveSize live = true) :
    sync (sync state live).state live =
      ⟨(sync state live).state, false⟩ := by
  by_cases same : state.window = live <;> simp [sync, valid, same]

end GxProofsGfx.Kernel.WindowResize
