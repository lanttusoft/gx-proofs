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
  gX — GUI Event Log Ring Buffer Specification

  Models the event ring buffer in src/gui/gui.c
  (idx = head % 64, head++/count++ — verified at gui.c:147-163;
  GX_GUI_EVENT_LOG_MAX = 64).

  Theorems proven: 6
    - mod64_in_bounds:          eventHead % 64 < 64 for any eventHead
    - mod64_valid_index:        eventHead % 64 is a valid index
    - dump_start_ge:            start = head - n when head >= n
    - dump_start_lt:            start = 0 when head < n
    - write_index_wraps:        head % 64 = (head + 64) % 64
    - slots_are_distinct:       64 writes fill all slots uniquely
-/

--ai: finite ring-slot witnesses are reduced inside the kernel.
namespace GxProofs.EventLog

def LOG_MAX : Nat := 64

theorem mod64_in_bounds (head : Nat) : head % LOG_MAX < LOG_MAX :=
  Nat.mod_lt head (by decide : 0 < 64)

theorem mod64_valid_index (head : Nat) : head % 64 < 64 :=
  Nat.mod_lt head (by decide : 0 < 64)

theorem dump_start_ge (head n : Nat) (h : head ≥ n) :
    (if head ≥ n then head - n else 0) = head - n := by
  simp [h]

theorem dump_start_lt (head n : Nat) (h : head < n) :
    (if head ≥ n then head - n else 0) = 0 := by
  have hnge : ¬ (head ≥ n) := by omega
  simp [hnge]

theorem write_index_wraps (head : Nat) : head % 64 = (head + 64) % 64 := by
  omega

theorem slots_are_distinct :
    (List.range 64).map (λ i => i % 64) = List.range 64 := by
  decide

end GxProofs.EventLog
