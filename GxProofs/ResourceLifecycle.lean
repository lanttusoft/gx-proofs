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
  gX — Resource Load/Unload Lifecycle Specification

  Salvaged from gameX lean/GameXProofs/ResourceLifecycle.lean.
  Models the Load/Unload pairing protocol for wrapper resources
  (every gX wrapper type pairs a Load path with an Unload path;
  double-load overwrites, double-unload is a no-op).

  Theorems proven: 8, all by rfl or simp.
-/

namespace GxProofs.ResourceLifecycle

inductive RS : Type where
  | none   : RS
  | loaded : Nat → RS
deriving DecidableEq, Repr

open RS

def load (s : RS) (id : Nat) : RS := loaded id
def unload (s : RS) : RS := RS.none

def getId (s : RS) : Nat :=
  match s with
  | RS.none    => 0
  | loaded id => id

theorem load_creates (id : Nat) (h : id > 0) : load RS.none id = loaded id := rfl

theorem unload_frees (id : Nat) (h : id > 0) : unload (loaded id) = RS.none := rfl

theorem load_unload_identity (id : Nat) (h : id > 0) : unload (load RS.none id) = RS.none := rfl

theorem double_load_overwrites (id1 id2 : Nat) :
    load (load RS.none id1) id2 = loaded id2 := rfl

theorem unload_empty_noop : unload RS.none = RS.none := rfl

theorem double_unload_noop (id : Nat) (h : id > 0) :
    unload (unload (loaded id)) = RS.none := rfl

theorem loaded_id_preserved (id : Nat) (h : id > 0) : getId (loaded id) = id := by
  simp [getId]

theorem reload_after_unload (id1 id2 : Nat) (h1 : id1 > 0) (h2 : id2 > 0) :
    load (unload (loaded id1)) id2 = loaded id2 := rfl

end GxProofs.ResourceLifecycle
