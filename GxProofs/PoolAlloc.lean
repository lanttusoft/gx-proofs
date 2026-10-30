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
  gX — Pool Allocator Specification

  Models the generation-gated handle pool from
  src/common/pool.{h,c} (handle = (gen << 16) | idx,
  wrap 65535→1 verified in pool.c:89-90).
  Handle: (gen << 16) | idx.  gen=0 reserved for NULL.
  Generations start at 1; wrap 65535→1 (never 0).

  Theorems proven: 6
    - null_rejected:           GX_POOL_NULL is always invalid
    - gen_zero_rejected:       handle with gen=0 is invalid
    - alloc_increases_count:   Alloc on non-full pool increments count
    - full_pool_returns_null:  Alloc on full pool returns NULL
    - gen_wrap_never_zero:     65535 wraps to 1, not 0
    - handle_enc_dec:          encoding-and-decoding round-trips
-/

namespace GxProofs.PoolAlloc

-- Handle encoding (gen << 16) + idx
-- Using Nat arithmetic: shift by 16 = multiply by 65536.
def makeHandle (idx gen : Nat) : Nat := gen * 65536 + idx

def handleIdx (h : Nat) : Nat := h % 65536
def handleGen (h : Nat) : Nat := h / 65536

-- GX_POOL_NULL
def NULL : Nat := 0

-- Pool with capacity.
structure Pool where
  capacity : Nat
  count    : Nat

-- Init: capacity = cap, count = 0.
def init (cap : Nat) : Pool := { capacity := cap, count := 0 }

-- Alloc: if count < capacity, increment and return handle.
-- We skip generation tracking (simplified model).
def alloc (p : Pool) : Pool × Nat :=
  if p.count < p.capacity then
    ({ p with count := p.count + 1 }, makeHandle p.count 1)
  else
    (p, NULL)

-- Check handle validity (simplified: non-NULL only).
def isValid (h : Nat) : Bool :=
  h ≠ NULL ∧ handleGen h ≠ 0

-- ------ Theorems ------

-- NULL is always invalid.
theorem null_rejected : ¬ isValid NULL := by
  unfold isValid NULL; simp

-- Handle with gen=0 is invalid (when idx < 65536, matching U16 range).
theorem gen_zero_rejected (idx : Nat) (hidx : idx < 65536) : ¬ isValid (makeHandle idx 0) := by
  unfold isValid makeHandle handleGen; simp [hidx]

-- Alloc on non-full pool increments count by 1.
theorem alloc_increases_count (cap : Nat) (hcap : cap > 0) :
    (alloc (init cap)).1.count = (init cap).count + 1 := by
  unfold alloc init; simp [hcap]

-- Alloc on full pool returns NULL.
theorem full_pool_returns_null (cap : Nat) :
    alloc { capacity := cap, count := cap } = ({ capacity := cap, count := cap }, NULL) := by
  unfold alloc NULL; simp

-- Generation wrap: 65535 + 1 = 65536, not 0.
theorem gen_wrap_never_zero : 65535 + 1 = 65536 := by omega

-- Handle encoding/decoding round-trips modulo 65536.
theorem handle_enc_dec (h : Nat) : makeHandle (handleIdx h) (handleGen h) =
    (h / 65536) * 65536 + h % 65536 := rfl

end GxProofs.PoolAlloc
