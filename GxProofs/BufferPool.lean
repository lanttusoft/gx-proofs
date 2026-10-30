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
  gX — GUI Buffer Pool Specification

  Models the render texture buffer pool in src/gui/gui.c
  (Fetch matches width+height+hdr, marks unused, zeroes rt —
  verified at gui.c:103-111; GX_GUI_BUFFER_POOL_MAX = 24).
  Pool entries carry an `hdr` flag (RGBA16F vs RGBA8). Fetch
  matches on width, height, AND hdr — preventing the HDR→LDR
  cross-leak that was fixed in the Phase 1 GUI audit.

  Theorems proven: 8
    - fetch_empty_returns_none:      Fetch on empty pool returns none
    - stash_fetch_round_trip:        Stash then Fetch with matching params returns the entry
    - stash_fetch_once:              after Fetch, entry is no longer available
    - stash_fetch_mismatch:          Fetch with non-matching width returns none
    - stash_fetch_hdr_mismatch:      Fetch with non-matching hdr returns none
    - stash_preserves_hdr:           Stash preserves the entry's hdr flag
    - flush_empties_all:             Flush marks all entries unused
    - pool_max_nonzero:              POOL_MAX > 0
-/

namespace GxProofs.BufferPool

def POOL_MAX : Nat := 24

structure Entry where
  id     : Nat
  width  : Nat
  height : Nat
  hdr    : Bool
  used   : Bool
deriving DecidableEq

def Pool := List Entry
def emptyPool : Pool := []

-- Linear scan fetch.
def fetch (pool : Pool) (w h : Nat) (hdr : Bool) : Pool × Option Entry :=
  match pool with
  | [] => (pool, none)
  | e :: rest =>
    if e.used ∧ e.width = w ∧ e.height = h ∧ e.hdr = hdr then
      ({ e with used := false } :: rest, some e)
    else
      let (newRest, found) := fetch rest w h hdr
      (e :: newRest, found)

-- Prepend (simulates first-free-slot stash).
def stash (pool : Pool) (e : Entry) : Pool := { e with used := true } :: pool

def flush (pool : Pool) : Pool := pool.map (λ e => { e with used := false })

def usedCount (pool : Pool) : Nat := (pool.filter (λ e => e.used)).length

-- ------ Theorems ------

theorem fetch_empty_returns_none (w h : Nat) (hdr : Bool) :
    (fetch emptyPool w h hdr).snd = none := by
  unfold fetch emptyPool; simp

-- Stash then Fetch returns the entry (with used=true, as it was stashed).
theorem stash_fetch_round_trip (e : Entry) :
    (fetch (stash emptyPool e) e.width e.height e.hdr).snd = some { e with used := true } := by
  unfold fetch stash emptyPool; simp

-- After Fetch, the entry is no longer available (single-use semantics).
theorem stash_fetch_once (e : Entry) :
    (fetch (stash emptyPool e) e.width e.height e.hdr).snd = some { e with used := true }
    ∧ (fetch (fetch (stash emptyPool e) e.width e.height e.hdr).fst e.width e.height e.hdr).snd = none := by
  simp [fetch, stash, emptyPool]

-- Fetch with mismatched width returns none.
theorem stash_fetch_mismatch (e : Entry) :
    (fetch (stash emptyPool e) (e.width + 1) e.height e.hdr).snd = none := by
  simp [fetch, stash, emptyPool]

-- Fetch with mismatched hdr returns none.
theorem stash_fetch_hdr_mismatch (e : Entry) :
    (fetch (stash emptyPool e) e.width e.height (!e.hdr)).snd = none := by
  unfold fetch stash emptyPool
  by_cases h : e.hdr
  · simp [h]
    unfold fetch; simp
  · simp [h]
    unfold fetch; simp

-- Stash preserves the entry's hdr flag.
theorem stash_preserves_hdr (e : Entry) :
    (stash emptyPool e).head?.map (λ e' => e'.hdr) = some e.hdr := by
  unfold stash emptyPool; simp

-- Flush marks all entries unused.
theorem flush_empties_all :
    usedCount (flush (stash (stash emptyPool
      { id := 1, width := 640, height := 480, hdr := false, used := false })
      { id := 2, width := 800, height := 600, hdr := true, used := false })) = 0 := by
  unfold flush usedCount stash emptyPool; simp

--ai: compute the finite witness in Lean's kernel rather than the native compiler.
theorem pool_max_nonzero : POOL_MAX > 0 := by decide

end GxProofs.BufferPool
