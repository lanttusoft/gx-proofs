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
  gX — RHI Buffer Management Specification

  Delete-zero guards verified in src/rhi/rhi_buf.c
  (VAO_Delete / Buffer_Delete skip id 0).

  Theorems proven: 4
    - vao_create_nonzero:   VAO_Create → result > 0
    - vao_delete_zero_noop: VAO_Delete(0) is no-op
    - vao_bind_sets:        VAO_Bind(id) → currentVAO = id
    - buf_create_nonzero:   Buffer_Create → result > 0
-/

namespace GxProofs.RhiBuf

structure State where
  vaos : List Nat
  currentVao : Nat
  buffers : List Nat
  currentBuf : Nat
  nextId : Nat
  nextPos : nextId > 0

def empty : State :=
  { vaos := [], currentVao := 0, buffers := [], currentBuf := 0, nextId := 1, nextPos := by decide }

def freshId (s : State) : Nat × State :=
  (s.nextId, { s with nextId := s.nextId + 1, nextPos := Nat.succ_pos s.nextId })

def vaoCreate (s : State) : State × Nat :=
  let (id, s') := freshId s; ({ s' with vaos := id :: s'.vaos }, id)

def vaoBind (s : State) (id : Nat) : State := { s with currentVao := id }

def vaoDelete (s : State) (id : Nat) : State :=
  if id = 0 then s else
  { s with vaos := s.vaos.erase id, currentVao := if s.currentVao = id then 0 else s.currentVao }

def bufCreate (s : State) : State × Nat :=
  let (id, s') := freshId s; ({ s' with buffers := id :: s'.buffers }, id)

theorem vao_create_nonzero (s : State) : (vaoCreate s).2 > 0 := by
  unfold vaoCreate freshId; simp [s.nextPos]

theorem vao_delete_zero_noop (s : State) : vaoDelete s 0 = s := by
  unfold vaoDelete; simp

theorem vao_bind_sets (s : State) (id : Nat) : (vaoBind s id).currentVao = id := by
  unfold vaoBind; simp

theorem buf_create_nonzero (s : State) : (bufCreate s).2 > 0 := by
  unfold bufCreate freshId; simp [s.nextPos]

end GxProofs.RhiBuf
