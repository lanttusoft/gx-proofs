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
  gX — RHI Raw Program Registry

  Models the raw-program table in src/rhi/gl_draw.c
  (GX_GL_RAW_MAX_PROGRAMS = 24, verified; Register dedups,
  zero is a no-op).

  Theorems proven: 7
    - register_adds:          Register(x) → x ∈ list (when space)
    - register_zero_noop:     Register(0) is no-op
    - unregister_removes:     Unregister(x) → x ∉ list
    - unregister_zero_noop:   Unregister(0) is no-op
    - isRaw_after_register:   after Register, IsRaw = true
    - isRaw_after_unregister: after Unregister, IsRaw = false
    - isRaw_zero_false:       IsRaw(0) = false
-/

namespace GxProofs.RhiProgramRegistry

def MAX : Nat := 24
abbrev State := List Nat
def empty : State := []

def register (s : State) (id : Nat) : State :=
  if id = 0 then s else if id ∈ s then s else if s.length ≥ MAX then s else id :: s

def unregister (s : State) (id : Nat) : State :=
  if id = 0 then s else s.filter (λ x => x ≠ id)

def isRaw (s : State) (id : Nat) : Bool := id ≠ 0 ∧ id ∈ s

theorem register_adds (s : State) (id : Nat) (h0 : id ≠ 0) (h_notmem : id ∉ s) (h_space : s.length < MAX) :
    id ∈ register s id := by
  unfold register
  by_cases h_eq0 : id = 0
  · exfalso; exact h0 h_eq0
  · by_cases h_mem : id ∈ s
    · exfalso; exact h_notmem h_mem
    · by_cases h_full : s.length ≥ MAX
      · exfalso; omega
      · simp [h_eq0, h_mem, h_full]

theorem register_zero_noop (s : State) : register s 0 = s := by
  unfold register; simp

theorem unregister_removes (s : State) (id : Nat) (h0 : id ≠ 0) (hm : id ∈ s) :
    id ∉ unregister s id := by
  unfold unregister; simp [h0, hm]

theorem unregister_zero_noop (s : State) : unregister s 0 = s := by
  unfold unregister; simp

theorem isRaw_after_register (s : State) (id : Nat) (h0 : id ≠ 0)
    (h_notmem : id ∉ s) (h_space : s.length < MAX) : isRaw (register s id) id := by
  unfold isRaw; have hm : id ∈ register s id := register_adds s id h0 h_notmem h_space; simp [hm, h0]

theorem isRaw_after_unregister (s : State) (id : Nat) (h0 : id ≠ 0) (hm : id ∈ s) :
    isRaw (unregister s id) id = false := by
  unfold isRaw; have h : id ∉ unregister s id := unregister_removes s id h0 hm; simp [h, h0]

theorem isRaw_zero_false (s : State) : isRaw s 0 = false := by
  unfold isRaw; simp

end GxProofs.RhiProgramRegistry
