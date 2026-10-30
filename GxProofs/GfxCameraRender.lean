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
  //ai: finite transaction model for the editor's two-tick camera render path.

  Models gfx_camera_render_tick in src/tools/gfx/gfx_editor.cpp for one
  accepted request. Views and marker visibility are Booleans standing for two
  abstract alternatives; the state space is finite. A pending tick either
  saves the authoring view/marker flag and applies the selected view, or fails
  without changing them when the selection is invalid. The next available tick
  attempts capture and restores both saved values whether capture succeeds or
  fails.

  A missing renderer makes the helper a no-op, so restoration is only proved
  when the applied phase receives a tick with a renderer. Scheduling skips
  (including free-camera mode), overlapping requests, image contents, file I/O,
  and successful GPU presentation are outside this model.
-/

namespace GxProofs.GfxCameraRender

inductive Phase where
  | idle
  | pending
  | applied
  | succeeded
  | failed
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  liveView : Bool
  markersVisible : Bool
  savedView : Bool
  savedMarkersVisible : Bool
  renderView : Bool
  captureAttempted : Bool
  deriving DecidableEq, Repr

def pendingRequest (liveView markersVisible renderView : Bool) : State :=
  ⟨.pending, liveView, markersVisible, false, false, renderView, false⟩

def tick (state : State) (rendererAvailable selectedCameraValid captureSucceeded : Bool) : State :=
  if rendererAvailable then
    if state.phase = .applied then { state with
      phase := if captureSucceeded then .succeeded else .failed
      liveView := state.savedView
      markersVisible := state.savedMarkersVisible
      captureAttempted := true
    } else if state.phase = .pending then
      if selectedCameraValid then { state with
        phase := .applied
        savedView := state.liveView
        savedMarkersVisible := state.markersVisible
        liveView := state.renderView
        markersVisible := false
      } else { state with phase := .failed }
    else state
  else state

theorem no_renderer_defers_state (state : State) (valid captureSucceeded : Bool) :
    tick state false valid captureSucceeded = state := by
  simp [tick]

theorem invalid_pending_camera_fails_without_mutation
    (liveView markersVisible renderView captureSucceeded : Bool) :
    let next := tick (pendingRequest liveView markersVisible renderView)
      true false captureSucceeded
    next.phase = .failed ∧
    next.liveView = liveView ∧
    next.markersVisible = markersVisible ∧
    next.captureAttempted = false := by
  simp [tick, pendingRequest]

theorem valid_pending_tick_saves_authoring_view
    (liveView markersVisible renderView captureSucceeded : Bool) :
    let next := tick (pendingRequest liveView markersVisible renderView)
      true true captureSucceeded
    next.phase = .applied ∧
    next.liveView = renderView ∧
    next.markersVisible = false ∧
    next.savedView = liveView ∧
    next.savedMarkersVisible = markersVisible ∧
    next.captureAttempted = false := by
  simp [tick, pendingRequest]

theorem applied_capture_restores_saved_state (state : State)
    (applied : state.phase = .applied) (captureSucceeded : Bool) :
    let next := tick state true false captureSucceeded
    next.liveView = state.savedView ∧
    next.markersVisible = state.savedMarkersVisible ∧
    next.captureAttempted = true ∧
    next.phase = if captureSucceeded then .succeeded else .failed := by
  simp [tick, applied]

theorem capture_failure_restores_authoring_state
    (liveView markersVisible renderView : Bool) :
    let pending := pendingRequest liveView markersVisible renderView
    let applied := tick pending true true false
    let failed := tick applied true true false
    failed.phase = .failed ∧
    failed.liveView = liveView ∧
    failed.markersVisible = markersVisible ∧
    failed.captureAttempted = true := by
  simp [tick, pendingRequest]

theorem valid_request_two_ticks_restore_authored_view
    (liveView markersVisible renderView captureSucceeded : Bool) :
    let pending := pendingRequest liveView markersVisible renderView
    let applied := tick pending true true captureSucceeded
    let finished := tick applied true true captureSucceeded
    finished.liveView = liveView ∧
    finished.markersVisible = markersVisible ∧
    finished.captureAttempted = true ∧
    finished.phase = if captureSucceeded then .succeeded else .failed := by
  simp [tick, pendingRequest]

theorem terminal_tick_does_not_retry (state : State)
    (terminal : state.phase = .succeeded ∨ state.phase = .failed)
    (captureSucceeded : Bool) :
    tick state true true captureSucceeded = state := by
  rcases terminal with terminal | terminal
  · simp [tick, terminal]
  · simp [tick, terminal]

theorem idle_tick_does_not_capture (state : State)
    (idle : state.phase = .idle) (captureSucceeded : Bool) :
    let next := tick state true true captureSucceeded
    next = state ∧ next.captureAttempted = state.captureAttempted := by
  simp [tick, idle]

end GxProofs.GfxCameraRender
