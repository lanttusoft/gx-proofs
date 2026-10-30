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
  gX — RHI Vertex Batch State Machine

  Models src/rhi/batch.c (MAX_VERTS = 8192, verified).

  Theorems proven: 6
    - begin_activates:   Begin → active, count=0
    - end_deactivates:   End → inactive, count=0
    - flush_resets:      Flush resets count when active and nonempty
    - settex_updates:    SetTexture → tex updated
    - settex_can_flush:  active+nonempty+diff → flush happens
    - vertex_advances:   Vertex increments count
-/

namespace GxProofs.RhiBatch

def MAX_VERTS : Nat := 8192
inductive BatchMode | quads | triangles | lines

structure State where
  active : Bool
  count : Nat
  cr : Nat
  cg : Nat
  cb : Nat
  ca : Nat
  cu : Float
  cv : Float
  currentTex : Nat

def empty : State :=
  { active := false, count := 0, cr := 255, cg := 255, cb := 255, ca := 255,
    cu := 0, cv := 0, currentTex := 0 }

def begin (s : State) (_m : BatchMode) : State :=
  { s with active := true, count := 0, cu := 0, cv := 0 }

def end_ (s : State) : State :=
  { s with active := false, count := 0, currentTex := 0 }

def flush (s : State) : State :=
  if ¬ s.active ∨ s.count = 0 then s else { s with count := 0 }

def setTexture (s : State) (tex : Nat) : State :=
  if s.active ∧ s.count > 0 ∧ tex ≠ s.currentTex then
    { (flush s) with currentTex := tex }
  else { s with currentTex := tex }

def vertex (s : State) : State :=
  if s.count + 1 ≥ MAX_VERTS then { (flush s) with count := 1 }
  else { s with count := s.count + 1 }

theorem begin_activates (s : State) (m : BatchMode) :
    (begin s m).active = true ∧ (begin s m).count = 0 := by
  unfold begin; simp

theorem end_deactivates (s : State) :
    (end_ s).active = false ∧ (end_ s).count = 0 := by
  unfold end_; simp

theorem flush_resets (s : State) (ha : s.active) (hc : s.count > 0) :
    (flush s).count = 0 := by
  unfold flush
  have hnz : s.count ≠ 0 := by omega
  simp [ha, hnz]

theorem settex_updates (s : State) (tex : Nat) : (setTexture s tex).currentTex = tex := by
  unfold setTexture
  by_cases h : s.active ∧ s.count > 0 ∧ tex ≠ s.currentTex
  · rcases h with ⟨ha, hc, hd⟩; simp [ha, hc, hd]
  · simp [h]

theorem settex_can_flush (s : State) (tex : Nat) (ha : s.active) (hc : s.count > 0)
    (hdiff : tex ≠ s.currentTex) : (setTexture s tex).count = 0 := by
  unfold setTexture
  have hcond : s.active ∧ s.count > 0 ∧ tex ≠ s.currentTex := ⟨ha, hc, hdiff⟩
  simp [hcond]
  unfold flush
  have hnz : s.count ≠ 0 := by omega
  simp [ha, hnz]

theorem vertex_advances (s : State) (hc : s.count + 1 < MAX_VERTS) :
    (vertex s).count = s.count + 1 := by
  unfold vertex
  have hnot : ¬ s.count + 1 ≥ MAX_VERTS := by omega
  simp [hnot]

end GxProofs.RhiBatch
