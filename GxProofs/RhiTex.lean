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
  gX — RHI Texture Lifecycle

  Delete-zero no-op verified in src/rhi/rhi_tex.c
  (gX_RHI_Tex_Delete guards texId == 0).

  Theorems proven: 5
    - create2D_nonzero:  valid dims → result > 0
    - create2D_zero_dim: 0 width or height → result = 0
    - delete_zero_noop:  Delete(0) is no-op
    - delete_removes:    Delete(id) removes id from state
    - param_binds:       Param(id) adds id to state
-/

namespace GxProofs.RhiTex

structure State where
  texIds : List Nat
def empty : State := { texIds := [] }

def allocId (s : State) : Nat :=
  match s.texIds with | [] => 1 | xs => xs.foldr max 0 + 1

def create2D (s : State) (w h : Nat) : State × Nat :=
  if w > 0 ∧ h > 0 then
    let id := allocId s; ({ texIds := id :: s.texIds }, id)
  else (s, 0)

def delete (s : State) (id : Nat) : State :=
  if id = 0 then s else { texIds := s.texIds.filter (λ x => x ≠ id) }

def param (s : State) (id : Nat) : State :=
  if id = 0 then s else if id ∈ s.texIds then s else { texIds := id :: s.texIds }

theorem allocId_pos (s : State) : allocId s > 0 := by
  unfold allocId; split <;> omega

theorem create2D_nonzero (s : State) (w h : Nat) (hw : w > 0) (hh : h > 0) :
    (create2D s w h).2 > 0 := by
  unfold create2D; simp [hw, hh]; apply allocId_pos

theorem create2D_zero_dim (s : State) (w h : Nat) (hz : w = 0 ∨ h = 0) :
    (create2D s w h).2 = 0 := by
  unfold create2D; rcases hz with (hw | hh)
  · rw [hw]; simp
  · rw [hh]; simp

theorem delete_zero_noop (s : State) : delete s 0 = s := by
  unfold delete; simp

theorem delete_removes (s : State) (id : Nat) (h : id ≠ 0) (hm : id ∈ s.texIds) :
    id ∉ (delete s id).texIds := by
  unfold delete; simp [h, hm]

theorem param_binds (s : State) (id : Nat) (h : id ≠ 0) (h_notmem : id ∉ s.texIds) :
    id ∈ (param s id).texIds := by
  unfold param; simp [h, h_notmem]

end GxProofs.RhiTex
