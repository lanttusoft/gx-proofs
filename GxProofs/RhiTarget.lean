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
  gX — RHI Texture Target Contract

  Models the target registry used by gX_RHI_Tex_Gen and the explicit target
  passed to gX_RHI_Tex_Bind.  The C wrapper is intentionally thin: OpenGL is
  responsible for rejecting a target mismatch.  This file proves the caller
  contracts used by the current gfx migration instead of pretending the
  wrapper performs validation itself.

  Theorems proven: 10
    - register_records_target: generated texture names retain their target
    - register_preserves_bound: registration does not disturb current binding
    - matching_bind_is_legal: registered target accepts the matching bind
    - mismatched_bind_is_illegal: registered target rejects a mismatched bind
    - bind_zero_clears: binding texture zero clears the current binding
    - matching_bind_succeeds: a legal bind updates the current binding
    - cluster_grid_target: cluster grid uses a 2D target
    - csm_array_target: CSM diagnostic readback uses an array target
    - shadow_map_target: cascade-zero diagnostic readback uses a 2D target
    - target_contract_examples: all three current migration paths are legal
-/

namespace GxProofs.RhiTarget

--opencode: mirror the three GL texture targets used by the migrated callers.
inductive TexTarget : Type where
  | tex2D
  | cube
  | array2D
deriving DecidableEq, Repr

structure State where
  targets : List (Nat × TexTarget)
  bound : Option (Nat × TexTarget)

def empty : State := { targets := [], bound := none }

--opencode: newest registration wins, matching the registry's update behavior.
def register (s : State) (id : Nat) (target : TexTarget) : State :=
  { s with targets := (id, target) :: s.targets }

def targetOf : List (Nat × TexTarget) → Nat → Option TexTarget
  | [], _ => none
  | (storedId, target) :: rest, id =>
      if storedId = id then some target else targetOf rest id

def bindLegal (s : State) (id : Nat) (target : TexTarget) : Bool :=
  if id = 0 then true
  else match targetOf s.targets id with
    | some stored => stored == target
    | none => false

--opencode: contract-level bind model; the production wrapper remains a thin
--   glBindTexture call and relies on OpenGL for mismatch errors.
def bind (s : State) (id : Nat) (target : TexTarget) : Option State :=
  if id = 0 then some { s with bound := none }
  else if bindLegal s id target then
    some { s with bound := some (id, target) }
  else none

theorem register_records_target (s : State) (id : Nat) (target : TexTarget) :
    targetOf (register s id target).targets id = some target := by
  simp [register, targetOf]

theorem register_preserves_bound (s : State) (id : Nat) (target : TexTarget) :
    (register s id target).bound = s.bound := by
  rfl

theorem matching_bind_is_legal (s : State) (id : Nat) (target : TexTarget) :
    bindLegal (register s id target) id target = true := by
  by_cases hzero : id = 0
  · simp [bindLegal, hzero]
  · simp [bindLegal, register, targetOf, hzero]

theorem mismatched_bind_is_illegal (s : State) (id : Nat)
    (stored requested : TexTarget) (hzero : id ≠ 0) (hmismatch : stored ≠ requested) :
    bindLegal (register s id stored) id requested = false := by
  simp [bindLegal, register, targetOf, hzero, hmismatch]

theorem bind_zero_clears (s : State) (target : TexTarget) :
    bind s 0 target = some { s with bound := none } := by
  simp [bind]

theorem matching_bind_succeeds (s : State) (id : Nat) (target : TexTarget)
    (hzero : id ≠ 0) :
    bind (register s id target) id target =
      some { (register s id target) with bound := some (id, target) } := by
  simp [bind, matching_bind_is_legal, hzero]

--opencode: symbolic nonzero texture names below are IDs, not texture units.
--   The production IDs are allocated dynamically; only their targets matter.
def clusterGrid : State := register empty 1 .tex2D

theorem cluster_grid_target :
    targetOf clusterGrid.targets 1 = some .tex2D := by
  simp [clusterGrid, empty, register, targetOf]

--opencode: current terrain CSM diagnostic path binds the shadow array as array2D.
def csmArray : State := register empty 2 .array2D

theorem csm_array_target :
    targetOf csmArray.targets 2 = some .array2D := by
  simp [csmArray, empty, register, targetOf]

--opencode: cascade-zero diagnostic depth map remains a plain 2D texture.
def cascadeZero : State := register empty 3 .tex2D

theorem shadow_map_target :
    targetOf cascadeZero.targets 3 = some .tex2D := by
  simp [cascadeZero, empty, register, targetOf]

theorem target_contract_examples :
    bindLegal clusterGrid 1 .tex2D = true ∧
    bindLegal csmArray 2 .array2D = true ∧
    bindLegal cascadeZero 3 .tex2D = true := by
  simp [clusterGrid, csmArray, cascadeZero, empty, register, bindLegal, targetOf]

end GxProofs.RhiTarget
