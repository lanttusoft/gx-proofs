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
  //ai: transactional drag-history algebra for captured before/after edit states.

  This finite model specifies only one authored value and the undo/redo stacks.
  It proves no-op preservation, one-entry commits for changed endpoints, endpoint
  restoration and redo invalidation by a subsequent changed edit. It does not
  prove the C++ editor's state capture, struct comparison, input handling or UI.
-/

import Mathlib.Tactic

namespace GxProofsGfx.Editor.DragHistory

structure History where
  current : Nat
  undo : List Nat
  redo : List Nat
  deriving DecidableEq, Repr

def commitDrag (history : History) (before after : Nat) : History :=
  if before = after then history
  else ⟨after, before :: history.undo, []⟩

def undo (history : History) : History :=
  match history.undo with
  | [] => history
  | previous :: rest => ⟨previous, rest, history.current :: history.redo⟩

def redo (history : History) : History :=
  match history.redo with
  | [] => history
  | next :: rest => ⟨next, history.current :: history.undo, rest⟩

theorem no_op_preserves_history (history : History) (value : Nat) :
    commitDrag history value value = history := by
  simp [commitDrag]

theorem changed_drag_pushes_one_start (history : History) (before after : Nat)
    (changed : before ≠ after) :
    commitDrag history before after = ⟨after, before :: history.undo, []⟩ := by
  simp [commitDrag, changed]

theorem undo_restores_drag_start (history : History) (after : Nat)
    (changed : history.current ≠ after) :
    (undo (commitDrag history history.current after)).current = history.current := by
  simp [commitDrag, undo, changed]

theorem redo_restores_drag_endpoint (history : History) (after : Nat)
    (changed : history.current ≠ after) :
    (redo (undo (commitDrag history history.current after))).current = after := by
  simp [commitDrag, undo, redo, changed]

theorem new_changed_drag_clears_redo (history : History) (first after : Nat)
    (firstChanged : history.current ≠ first)
    (newChanged : history.current ≠ after) :
    (commitDrag (undo (commitDrag history history.current first))
      history.current after).redo = [] := by
  simp [commitDrag, undo, firstChanged, newChanged]

theorem no_op_after_undo_preserves_redo (history : History) (first : Nat)
    (changed : history.current ≠ first) :
    (commitDrag (undo (commitDrag history history.current first))
      history.current history.current).redo = [first] := by
  simp [commitDrag, undo, changed]

end GxProofsGfx.Editor.DragHistory
