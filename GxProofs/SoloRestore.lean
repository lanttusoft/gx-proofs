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
  gX — Solo isolate stash/restore specification

  Models the DRAW-flag stash cycle from
  src/tools/editor/editor.cpp (tools_solo_restore): on restore,
  each surviving element regains its stashed flag
  (DRAW = stash[ei] for ei below both counts), elements past the stash
  keep theirs, and the stash is freed (single-shot — a second restore
  is a no-op).

  Proven here: exact-count restore is the identity (the "solo leaves
  the canvas hidden" class cannot survive a matched stash), the length
  law for count mismatches (re-stash on selection/canvas change keeps
  the table sized), and both empty edges (null stash ≈ empty, empty
  canvas) which are the early-return paths in C.

  Theorems proven: 4
    - restore_exact:        matched counts restore every flag
    - restore_length:       mismatched counts keep the longer length
    - restore_empty_stash:  empty stash restores flags untouched
    - restore_empty_flags:  empty canvas restores to empty
-/

namespace GxProofs.SoloRestore

-- tools_solo_restore write-back: stashed prefix, surviving tail.
def restore (stash flags : List Bool) : List Bool :=
  stash.take flags.length ++ flags.drop stash.length

-- 1. Matched stash restores every flag (full recovery).
theorem restore_exact (s f : List Bool) (h : s.length = f.length) :
    restore s f = s := by
  unfold restore
  rw [← h, List.take_length, h, List.drop_length, List.append_nil]

-- 2. Length law: restore keeps the canvas count — the stash only ever
-- overwrites a prefix, so a short stash cannot shrink the canvas and
-- a long stash cannot grow it (the re-stash sizing discipline).
theorem restore_length (s f : List Bool) :
    (restore s f).length = f.length := by
  unfold restore
  rw [List.length_append, List.length_take, List.length_drop]
  omega

-- 3. Empty stash (null-stash early path): flags pass through.
theorem restore_empty_stash (f : List Bool) : restore [] f = f := by
  unfold restore
  rw [List.take_nil, List.length_nil, List.drop_zero, List.nil_append]

-- 4. Empty canvas (zero-element loop no-op): restore is empty.
theorem restore_empty_flags (s : List Bool) : restore s [] = [] := by
  unfold restore
  rw [List.length_nil, List.take_zero, List.drop_nil, List.append_nil]
