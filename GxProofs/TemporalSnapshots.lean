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
  //ai: source-grounded snapshot assignments, with an explicit ghost history camera.
  motionblur.c writes motionBlurPrevVP during the frame; gfx_pipeline.c writes
  both snapshots only at pipeline completion. taa.c reads its private taaPrevVP.
  Labels stand for matrices. historyCamera is proof-only provenance, not a C
  field. Pipeline scheduling, successful draws/clears, and frame chronology are
  assumptions; a saved VP is not automatically the camera of retained history.
-/
import GxProofs.TemporalHistory

namespace GxProofs.TemporalSnapshots
open TemporalHistory

structure State where
  taaVP : Nat
  motionVP : Nat
  temporal : TemporalHistory.State
  historyCamera : Option Nat

def initial (identity : Nat) : State := ⟨identity, identity, TemporalHistory.initial, none⟩
def motionBlur (s : State) (current : Nat) : State := { s with motionVP := current }
def finishFrame (s : State) (current : Nat) : State :=
  { s with taaVP := current, motionVP := current }
def resetHistory (s : State) : State :=
  { s with temporal := reset s.temporal, historyCamera := none }
def commitHistory (s : State) (current : Nat) : State :=
  if s.temporal.passActive then
    { s with temporal := commitPass s.temporal, historyCamera := some current }
  else s

def Aligned (s : State) : Prop :=
  s.temporal.historyValid = true → s.historyCamera = some s.taaVP

theorem motion_blur_preserves_taa (s : State) (current : Nat) :
    (motionBlur s current).taaVP = s.taaVP := rfl

theorem motion_blur_preserves_history (s : State) (current : Nat) :
    (motionBlur s current).temporal = s.temporal ∧
    (motionBlur s current).historyCamera = s.historyCamera := by simp [motionBlur]

theorem end_frame_records_current (s : State) (current : Nat) :
    (finishFrame s current).taaVP = current ∧ (finishFrame s current).motionVP = current := by
  simp [finishFrame]

theorem end_frame_does_not_commit_history (s : State) (current : Nat) :
    (finishFrame s current).temporal = s.temporal ∧
    (finishFrame s current).historyCamera = s.historyCamera := by simp [finishFrame]

theorem next_frame_private_snapshot (s : State) (previous current : Nat) :
    (motionBlur (finishFrame s previous) current).taaVP = previous ∧
    (motionBlur (finishFrame s previous) current).motionVP = current := by
  simp [motionBlur, finishFrame]

theorem reset_does_not_rewrite_snapshots (s : State) :
    (resetHistory s).taaVP = s.taaVP ∧ (resetHistory s).motionVP = s.motionVP := by
  simp [resetHistory]

theorem reset_invalidates_provenance (s : State) :
    (resetHistory s).temporal.historyValid = false ∧
    (resetHistory s).historyCamera = none := by simp [resetHistory, reset, TemporalHistory.initial]

theorem reset_aligned_vacuously (s : State) : Aligned (resetHistory s) := by
  simp [Aligned, resetHistory, reset, TemporalHistory.initial]

theorem committed_frame_aligned (s : State) (current : Nat)
    (hp : s.temporal.passActive = true) : Aligned (finishFrame (commitHistory s current) current) := by
  simp [Aligned, finishFrame, commitHistory, hp]

theorem motion_blur_preserves_alignment (s : State) (current : Nat) (h : Aligned s) :
    Aligned (motionBlur s current) := h

--ai: successful resolve and end-of-frame save must refer to the SAME camera.
theorem mismatched_camera_not_aligned (s : State) (resolved saved : Nat)
    (hp : s.temporal.passActive = true) (h : resolved ≠ saved) :
    ¬ Aligned (finishFrame (commitHistory s resolved) saved) := by
  simp [Aligned, finishFrame, commitHistory, commitPass, hp, h]

--ai: retained raster history after skipped resolves need not match the last pipeline VP.
theorem skipped_resolve_counterexample :
    let s : State := ⟨10, 10, ⟨1,true,false,false,true⟩, some 10⟩
    Aligned s ∧ ¬ Aligned (finishFrame s 11) := by
  simp [Aligned, finishFrame]

--ai: frame labels model non-wrapping chronology; runtime consecutiveness is a UInt64 comparison input.
structure TimedState where
  snapshot : State
  lastResolveFrame : Nat

def commitTimed (s : TimedState) (frame camera : Nat) : TimedState :=
  if s.snapshot.temporal.passActive then
    ⟨commitHistory s.snapshot camera, frame⟩
  else s

def abortTimed (s : TimedState) : TimedState :=
  { s with snapshot := { s.snapshot with temporal := abortPass s.snapshot.temporal } }

--ai: models invalidation before the C caller clears both targets and marks them cleared.
def prepareTimed (s : TimedState) (consecutive : Bool) : TimedState :=
  if needsHistoryReset false false true s.snapshot.temporal.historyValid consecutive then
    { s with snapshot := resetHistory s.snapshot }
  else s

theorem idle_commit_preserves_stamp (s : TimedState) (frame camera : Nat)
    (h : s.snapshot.temporal.passActive = false) : commitTimed s frame camera = s := by
  simp [commitTimed, h]

theorem active_commit_records_frame (s : TimedState) (frame camera : Nat)
    (h : s.snapshot.temporal.passActive = true) :
    (commitTimed s frame camera).lastResolveFrame = frame := by simp [commitTimed, h]

theorem abort_preserves_stamp (s : TimedState) :
    (abortTimed s).lastResolveFrame = s.lastResolveFrame := rfl

theorem commit_after_abort_preserves_stamp (s : TimedState) (frame camera : Nat) :
    commitTimed (abortTimed s) frame camera = abortTimed s := by
  simp [commitTimed, abortTimed, abortPass]

theorem gap_invalidates_history (s : TimedState) (h : s.snapshot.temporal.historyValid = true) :
    (prepareTimed s false).snapshot.temporal.historyValid = false ∧
    (prepareTimed s false).snapshot.historyCamera = none := by
  simp [prepareTimed, needsHistoryReset, h, resetHistory, reset, TemporalHistory.initial]

theorem gap_reestablishes_vacuous_alignment (s : TimedState)
    (h : s.snapshot.temporal.historyValid = true) : Aligned (prepareTimed s false).snapshot := by
  simp [prepareTimed, needsHistoryReset, h]
  exact reset_aligned_vacuously s.snapshot

theorem prepare_does_not_advance_stamp (s : TimedState) (consecutive : Bool) :
    (prepareTimed s consecutive).lastResolveFrame = s.lastResolveFrame := by
  unfold prepareTimed
  split <;> rfl

end GxProofs.TemporalSnapshots
