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
  gX — temporal-history lifecycle contract

  //ai: Grounded in src/renderer/gfx/temporal_history.c and the reset
  predicate in taa.c. Begin rejection preserves state AND the output pair;
  MarkCleared deliberately leaves passActive/index/parity unchanged.

  Checked begin rejects identical wrappers and shared/zero FBO or color names.
  GPU attachment/cache coherence and successful clearing/rendering remain caller
  obligations. Nat models reachable nonnegative indices; bounded commit wraps
  at the signed maximum. Arbitrary negative C state is not represented.
  Reset-policy inputs are the actual signature-equality and UInt64 successor
  comparisons; no hash collision-freedom or unbounded frame chronology is claimed.
-/

namespace GxProofs.TemporalHistory

structure State where
  frameIndex : Nat
  historyValid : Bool
  clearPending : Bool
  passActive : Bool
  parity : Bool
deriving DecidableEq, Repr

structure Targets where
  read : Nat
  write : Nat
deriving DecidableEq, Repr

structure BeginResult where
  state : State
  targets : Targets
  accepted : Bool
deriving DecidableEq, Repr

def initial : State := ⟨0, false, true, false, false⟩
def reset (_s : State) : State := initial
def markCleared (s : State) : State :=
  { s with clearPending := false, historyValid := false }

def selectTargets (s : State) (a b : Nat) : Targets :=
  if s.parity then ⟨b, a⟩ else ⟨a, b⟩

def currentTarget (s : State) (a b : Nat) : Nat :=
  if s.parity then b else a

def canBegin (s : State) (loadedA loadedB pointersValid : Bool) : Bool :=
  !s.clearPending && !s.passActive && loadedA && loadedB && pointersValid

def beginPass (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) : BeginResult :=
  if canBegin s loadedA loadedB pointersValid then
    ⟨{ s with passActive := true }, selectTargets s a b, true⟩
  else ⟨s, output, false⟩

--ai: bounded index, not an unbounded lifetime accumulation count.
def signedCounterMax : Nat := 2147483647
def nextFrame (index : Nat) : Nat := if index < signedCounterMax then index + 1 else 0

def commitPass (s : State) : State :=
  if s.passActive then
    { s with historyValid := true, parity := !s.parity,
             frameIndex := nextFrame s.frameIndex, passActive := false }
  else s

def abortPass (s : State) : State := { s with passActive := false }

def needsClearNullable (s : Option State) : Bool :=
  match s with | none => false | some history => history.clearPending

def frameIndexNullable (s : Option State) : Nat :=
  match s with | none => 0 | some history => history.frameIndex

def currentTargetNullable (s : Option State) (a b : Nat) : Nat :=
  match s with | none => a | some history => currentTarget history a b

--ai: consecutive is the actual UInt64 comparison to the last COMMITTED resolve, not the last entry.
def needsHistoryReset (active wasActive sameSignature historyValid consecutive : Bool) : Bool :=
  (active != wasActive) || (active && !sameSignature) || (historyValid && !consecutive)

--ai: convenience specialization for already-valid history; applies to raster as well as hybrid.
def needsHybridReset (active wasActive sameSignature consecutive : Bool) : Bool :=
  needsHistoryReset active wasActive sameSignature true consecutive

theorem initial_contract :
    initial.frameIndex = 0 ∧ initial.historyValid = false ∧
    initial.clearPending = true ∧ initial.passActive = false ∧ initial.parity = false := by
  decide

theorem reset_discards_history (s : State) : reset s = initial := rfl

theorem reset_idempotent (s : State) : reset (reset s) = reset s := rfl

theorem clearing_invalidates_only (s : State) :
    (markCleared s).clearPending = false ∧ (markCleared s).historyValid = false ∧
    (markCleared s).passActive = s.passActive ∧
    (markCleared s).frameIndex = s.frameIndex ∧ (markCleared s).parity = s.parity := by
  simp [markCleared]

theorem clearing_idempotent (s : State) : markCleared (markCleared s) = markCleared s := rfl

theorem pending_rejects_begin (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) (h : s.clearPending = true) :
    beginPass s loadedA loadedB pointersValid a b output = ⟨s, output, false⟩ := by
  simp [beginPass, canBegin, h]

theorem active_rejects_begin (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) (h : s.passActive = true) :
    beginPass s loadedA loadedB pointersValid a b output = ⟨s, output, false⟩ := by
  simp [beginPass, canBegin, h]

theorem unloaded_a_rejects (s : State) (loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) :
    beginPass s false loadedB pointersValid a b output = ⟨s, output, false⟩ := by
  simp [beginPass, canBegin]

theorem unloaded_b_rejects (s : State) (loadedA pointersValid : Bool)
    (a b : Nat) (output : Targets) :
    beginPass s loadedA false pointersValid a b output = ⟨s, output, false⟩ := by
  simp [beginPass, canBegin]

theorem missing_pointer_rejects (s : State) (loadedA loadedB : Bool)
    (a b : Nat) (output : Targets) :
    beginPass s loadedA loadedB false a b output = ⟨s, output, false⟩ := by
  simp [beginPass, canBegin]

theorem ready_begin_contract (s : State) (a b : Nat) (output : Targets)
    (hc : s.clearPending = false) (hp : s.passActive = false) :
    beginPass s true true true a b output =
      ⟨{ s with passActive := true }, selectTargets s a b, true⟩ := by
  simp [beginPass, canBegin, hc, hp]

theorem rejected_begin_preserves_everything (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) (h : canBegin s loadedA loadedB pointersValid = false) :
    beginPass s loadedA loadedB pointersValid a b output = ⟨s, output, false⟩ := by
  simp [beginPass, h]

theorem begin_preserves_prior_history (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) :
    (beginPass s loadedA loadedB pointersValid a b output).state.frameIndex = s.frameIndex ∧
    (beginPass s loadedA loadedB pointersValid a b output).state.historyValid = s.historyValid ∧
    (beginPass s loadedA loadedB pointersValid a b output).state.clearPending = s.clearPending ∧
    (beginPass s loadedA loadedB pointersValid a b output).state.parity = s.parity := by
  by_cases h : canBegin s loadedA loadedB pointersValid = true <;> simp [beginPass, h]

theorem accepted_begin_rejects_nested (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output nestedOutput : Targets) (h : canBegin s loadedA loadedB pointersValid = true) :
    beginPass (beginPass s loadedA loadedB pointersValid a b output).state
      true true true a b nestedOutput =
      ⟨{ s with passActive := true }, nestedOutput, false⟩ := by
  have started : beginPass s loadedA loadedB pointersValid a b output =
      ⟨{ s with passActive := true }, selectTargets s a b, true⟩ := by
    simp [beginPass, h]
  rw [started]
  exact active_rejects_begin { s with passActive := true } true true true a b nestedOutput rfl

theorem first_begin_reads_a_writes_b (a b : Nat) (output : Targets) :
    beginPass (markCleared initial) true true true a b output =
      ⟨{ (markCleared initial) with passActive := true }, ⟨a, b⟩, true⟩ := by
  simp [beginPass, canBegin, markCleared, initial, selectTargets]

theorem current_is_read_target (s : State) (a b : Nat) :
    currentTarget s a b = (selectTargets s a b).read := by
  cases h : s.parity <;> simp [currentTarget, selectTargets, h]

theorem distinct_targets_require_distinct_labels (s : State) (a b : Nat) (h : a ≠ b) :
    (selectTargets s a b).read ≠ (selectTargets s a b).write := by
  cases hp : s.parity <;> simp [selectTargets, hp, h, Ne.symm h]

theorem aliased_targets_are_not_rejected_by_selection (s : State) (a : Nat) :
    selectTargets s a a = ⟨a, a⟩ := by
  cases h : s.parity <;> simp [selectTargets, h]

theorem idle_commit_noop (s : State) (h : s.passActive = false) : commitPass s = s := by
  simp [commitPass, h]

theorem active_commit_contract (s : State) (h : s.passActive = true) :
    commitPass s = { s with historyValid := true, parity := !s.parity, frameIndex := nextFrame s.frameIndex, passActive := false } := by
  simp [commitPass, h]

theorem commit_idempotent (s : State) : commitPass (commitPass s) = commitPass s := by
  cases h : s.passActive <;> simp [commitPass, h]

theorem committed_current_is_written_target (s : State) (a b : Nat) (h : s.passActive = true) :
    currentTarget (commitPass s) a b = (selectTargets s a b).write := by
  cases hp : s.parity <;> simp [commitPass, currentTarget, selectTargets, h, hp]

theorem abort_preserves_history (s : State) :
    (abortPass s).frameIndex = s.frameIndex ∧ (abortPass s).historyValid = s.historyValid ∧
    (abortPass s).clearPending = s.clearPending ∧ (abortPass s).parity = s.parity ∧
    (abortPass s).passActive = false := by
  simp [abortPass]

theorem abort_idempotent (s : State) : abortPass (abortPass s) = abortPass s := rfl

theorem commit_after_abort_noop (s : State) : commitPass (abortPass s) = abortPass s := by
  simp [commitPass, abortPass]

--ai: clear-before-use is an inductive caller invariant, not a property of arbitrary corrupt states.
def WellFormed (s : State) : Prop :=
  s.clearPending = true → s.historyValid = false ∧ s.passActive = false

theorem initial_well_formed : WellFormed initial := by simp [WellFormed, initial]

theorem reset_well_formed (s : State) : WellFormed (reset s) := initial_well_formed

theorem clearing_well_formed (s : State) : WellFormed (markCleared s) := by
  simp [WellFormed, markCleared]

theorem begin_preserves_well_formed (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (output : Targets) (hw : WellFormed s) :
    WellFormed (beginPass s loadedA loadedB pointersValid a b output).state := by
  intro pending
  have samePending := (begin_preserves_prior_history s loadedA loadedB pointersValid a b output).2.2.1
  rw [samePending] at pending
  have rejected := pending_rejects_begin s loadedA loadedB pointersValid a b output pending
  simpa [rejected] using hw pending

theorem abort_preserves_well_formed (s : State) (hw : WellFormed s) :
    WellFormed (abortPass s) := by
  intro pending
  exact ⟨(hw pending).1, rfl⟩

theorem commit_preserves_well_formed (s : State) (hw : WellFormed s) :
    WellFormed (commitPass s) := by
  by_cases hp : s.passActive = true
  · have hc : s.clearPending = false := by
      cases pending : s.clearPending
      · rfl
      · have inactive := (hw pending).2
        simp [hp] at inactive
    simp [WellFormed, commitPass, hp, hc]
  · simpa [commitPass, hp] using hw

theorem commit_does_not_validate_clear_state :
    (commitPass { initial with passActive := true }).historyValid = true ∧
    (commitPass { initial with passActive := true }).clearPending = true := by
  decide

--ai: active commit is bounded even at the maximum; idle commit still preserves state.
theorem next_frame_bounded (index : Nat) : nextFrame index ≤ signedCounterMax := by
  unfold nextFrame
  split <;> omega

theorem bounded_active_commit (s : State) (hp : s.passActive = true) :
    (commitPass s).frameIndex ≤ signedCounterMax := by
  rw [active_commit_contract s hp]
  exact next_frame_bounded s.frameIndex

theorem commit_at_max_wraps :
    (commitPass { initial with frameIndex := signedCounterMax, passActive := true }).frameIndex = 0 := by
  simp [commitPass, initial, nextFrame]

theorem increment_below_max (index : Nat) (h : index < signedCounterMax) :
    nextFrame index = index + 1 := by simp [nextFrame, h]

--ai: labels are wrapper identities and GL names, not evidence of driver attachment coherence.
structure Backing where
  fbo : Nat
  color : Nat
deriving DecidableEq

def independent (a b : Nat) (ba bb : Backing) : Prop :=
  a ≠ b ∧ ba.fbo ≠ 0 ∧ bb.fbo ≠ 0 ∧ ba.color ≠ 0 ∧ bb.color ≠ 0 ∧
  ba.fbo ≠ bb.fbo ∧ ba.color ≠ bb.color

instance (a b : Nat) (ba bb : Backing) : Decidable (independent a b ba bb) := by
  unfold independent
  infer_instance

--ai: beginPass above is the selection core; this wrapper models the hardened C entry point.
def beginCheckedPass (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets) : BeginResult :=
  if independent a b ba bb then beginPass s loadedA loadedB pointersValid a b output
  else ⟨s, output, false⟩

theorem invalid_backing_rejects (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets) (h : ¬ independent a b ba bb) :
    beginCheckedPass s loadedA loadedB pointersValid a b ba bb output = ⟨s, output, false⟩ := by
  simp [beginCheckedPass, h]

theorem accepted_checked_begin_independent (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets)
    (h : (beginCheckedPass s loadedA loadedB pointersValid a b ba bb output).accepted = true) :
    independent a b ba bb := by
  by_cases hi : independent a b ba bb
  · exact hi
  · simp [beginCheckedPass, hi] at h

theorem same_wrapper_rejected (s : State) (loadedA loadedB pointersValid : Bool)
    (a : Nat) (ba bb : Backing) (output : Targets) :
    beginCheckedPass s loadedA loadedB pointersValid a a ba bb output = ⟨s, output, false⟩ := by
  simp [beginCheckedPass, independent]

theorem shared_color_rejected (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets) (h : ba.color = bb.color) :
    beginCheckedPass s loadedA loadedB pointersValid a b ba bb output = ⟨s, output, false⟩ := by
  simp [beginCheckedPass, independent, h]

theorem shared_fbo_rejected (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets) (h : ba.fbo = bb.fbo) :
    beginCheckedPass s loadedA loadedB pointersValid a b ba bb output = ⟨s, output, false⟩ := by
  simp [beginCheckedPass, independent, h]

theorem valid_checked_begin_matches_selection (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets) (h : independent a b ba bb) :
    beginCheckedPass s loadedA loadedB pointersValid a b ba bb output =
      beginPass s loadedA loadedB pointersValid a b output := by
  simp [beginCheckedPass, h]

theorem accepted_checked_targets_distinct (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets)
    (h : (beginCheckedPass s loadedA loadedB pointersValid a b ba bb output).accepted = true) :
    (beginCheckedPass s loadedA loadedB pointersValid a b ba bb output).targets.read ≠
      (beginCheckedPass s loadedA loadedB pointersValid a b ba bb output).targets.write := by
  have hi := accepted_checked_begin_independent s loadedA loadedB pointersValid a b ba bb output h
  by_cases hc : canBegin s loadedA loadedB pointersValid = true
  · simpa [beginCheckedPass, hi, beginPass, hc] using
      distinct_targets_require_distinct_labels s a b hi.1
  · simp [beginCheckedPass, hi, beginPass, hc] at h

theorem checked_begin_preserves_well_formed (s : State) (loadedA loadedB pointersValid : Bool)
    (a b : Nat) (ba bb : Backing) (output : Targets) (hw : WellFormed s) :
    WellFormed (beginCheckedPass s loadedA loadedB pointersValid a b ba bb output).state := by
  by_cases hi : independent a b ba bb
  · simpa [beginCheckedPass, hi] using
      begin_preserves_well_formed s loadedA loadedB pointersValid a b output hw
  · simpa [beginCheckedPass, hi] using hw

theorem nullable_queries_safe (a b : Nat) :
    needsClearNullable none = false ∧ frameIndexNullable none = 0 ∧
    currentTargetNullable none a b = a := by
  simp [needsClearNullable, frameIndexNullable, currentTargetNullable]

theorem routing_change_resets (sameSignature consecutive : Bool) :
    needsHybridReset true false sameSignature consecutive = true ∧
    needsHybridReset false true sameSignature consecutive = true := by
  simp [needsHybridReset, needsHistoryReset]

theorem stable_active_history_kept : needsHybridReset true true true true = false := by decide

theorem authored_change_resets (consecutive : Bool) :
    needsHybridReset true true false consecutive = true := by simp [needsHybridReset, needsHistoryReset]

theorem skipped_resolve_resets (sameSignature : Bool) :
    needsHybridReset true true sameSignature false = true := by simp [needsHybridReset, needsHistoryReset]

theorem inactive_consecutive_history_ignores_sdf_changes (sameSignature : Bool) :
    needsHybridReset false false sameSignature true = false := by simp [needsHybridReset, needsHistoryReset]

theorem raster_gap_resets (sameSignature : Bool) :
    needsHistoryReset false false sameSignature true false = true := by simp [needsHistoryReset]

theorem invalid_history_does_not_need_gap_reset (sameSignature consecutive : Bool) :
    needsHistoryReset false false sameSignature false consecutive = false := by simp [needsHistoryReset]

end GxProofs.TemporalHistory
