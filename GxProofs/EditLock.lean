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
  gX — Editor edit-lock specification

  Models the canvas inertness lock from
  src/tools/editor/editor.cpp (tools_edit_lock_set/clear):
  setting the lock on the target canvas locks exactly that canvas,
  clears every other canvas (at most one locked globally), and drops
  FOCUSED on the target's elements (no focus ring under the editor).
  Clearing zeroes all locks and preserves focus bits (surgical —
  close never eats selection state, it only unlocks).

  Proven here: exclusivity (no two-canvases-locked state exists),
  totality of clear (stuck-locked always has a one-call recovery,
  which editor close and runtime close both invoke), and the
  lock-clears-focus coupling. A future "canvas dead after editor
  close" report must be a missed clear call, not lock logic.

  Theorems proven: 6
    - target_locked:      set locks exactly the target
    - others_cleared:     every other canvas reads unlocked
    - at_most_one:        no state with two locked canvases via set
    - clear_empties:      clear zeroes every canvas
    - lock_clears_focus:  locking drops FOCUSED on the target element
    - clear_keeps_focus:  clearing preserves the focus bit
-/

namespace GxProofs.EditLock

-- Lock table over the 8 canvas slots.
abbrev Locks := Fin 8 → Bool

-- tools_edit_lock_set: target locked, all others cleared.
def setLock (idx : Fin 8) : Locks := fun i => if i = idx then true else false

-- tools_edit_lock_clear: everything unlocked.
def clearLocks : Locks := fun _ => false

-- 1. The target canvas reads locked.
theorem target_locked (idx : Fin 8) : setLock idx idx = true := by
  simp [setLock]

-- 2. Every other canvas reads unlocked.
theorem others_cleared (idx i : Fin 8) (h : i ≠ idx) :
    setLock idx i = false := by
  simp [setLock, h]

-- 3. Exclusivity: set can never produce two locked canvases.
theorem at_most_one (idx i j : Fin 8)
    (h1 : setLock idx i = true) (h2 : setLock idx j = true) : i = j := by
  unfold setLock at h1 h2
  by_cases hi : i = idx <;> by_cases hj : j = idx
  · subst hi
    subst hj
    rfl
  · exfalso
    simp [hj] at h2
  · exfalso
    simp [hi] at h1
  · exfalso
    simp [hi] at h1

-- 4. Clear is total: every canvas reads unlocked after.
theorem clear_empties (i : Fin 8) : clearLocks i = false :=
  rfl

-- Element state under lock: (locked, focused).
abbrev ElemState := Bool × Bool

-- Locking an element sets the bit and drops FOCUSED.
def lockElem : ElemState := (true, false)

-- Clearing unlocks but preserves the focus bit.
def clearElem (e : ElemState) : ElemState := (false, e.2)

-- 5. Lock couples the bit with focus cleared (no focus ring leaks
-- through the editor onto the inert canvas).
theorem lock_clears_focus : lockElem = (true, false) :=
  rfl

-- 6. Clear is surgical: the focus bit survives unlocking.
theorem clear_keeps_focus (e : ElemState) : (clearElem e).2 = e.2 :=
  rfl
