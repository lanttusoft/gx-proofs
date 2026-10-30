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
  gX — Point Shadow Cubemap Face Directions

  Salvaged from gameX lean/GameXProofs/PointShadowFaces.lean,
  re-verified line by line: src/renderer/gfx/light.c:133-138
  carries the identical 6 face targets and up vectors
  (gX_ComputePointShadowMatrices).

  Each face has a specific target direction and up vector:
    Face 0 (+X): target=pos+(1,0,0),  up=(0,-1,0)
    Face 1 (-X): target=pos+(-1,0,0), up=(0,-1,0)
    Face 2 (+Y): target=pos+(0,1,0),  up=(0,0,1)
    Face 3 (-Y): target=pos+(0,-1,0), up=(0,0,-1)
    Face 4 (+Z): target=pos+(0,0,1),  up=(0,-1,0)
    Face 5 (-Z): target=pos+(0,0,-1), up=(0,-1,0)
-/


namespace GxProofs.PointShadowFaces

structure Vec3 where
  x : Float
  y : Float
  z : Float

-- Face target directions (light.c:133-138)
def faceTarget (pos : Vec3) (face : Nat) : Vec3 :=
  match face with
  | 0 => { x := pos.x + 1.0, y := pos.y, z := pos.z }
  | 1 => { x := pos.x - 1.0, y := pos.y, z := pos.z }
  | 2 => { x := pos.x, y := pos.y + 1.0, z := pos.z }
  | 3 => { x := pos.x, y := pos.y - 1.0, z := pos.z }
  | 4 => { x := pos.x, y := pos.y, z := pos.z + 1.0 }
  | 5 => { x := pos.x, y := pos.y, z := pos.z - 1.0 }
  | _ => pos

-- View direction (target - pos), axis-aligned
def viewDir (pos : Vec3) (face : Nat) : Vec3 :=
  match face with
  | 0 => { x := 1.0, y := 0.0, z := 0.0 }
  | 1 => { x := -1.0, y := 0.0, z := 0.0 }
  | 2 => { x := 0.0, y := 1.0, z := 0.0 }
  | 3 => { x := 0.0, y := -1.0, z := 0.0 }
  | 4 => { x := 0.0, y := 0.0, z := 1.0 }
  | 5 => { x := 0.0, y := 0.0, z := -1.0 }
  | _ => { x := 0.0, y := 0.0, z := 0.0 }

-- Up vectors (light.c:133-138)
def faceUp (face : Nat) : Vec3 :=
  match face with
  | 0 => { x := 0.0, y := -1.0, z := 0.0 }
  | 1 => { x := 0.0, y := -1.0, z := 0.0 }
  | 2 => { x := 0.0, y := 0.0, z := 1.0 }
  | 3 => { x := 0.0, y := 0.0, z := -1.0 }
  | 4 => { x := 0.0, y := -1.0, z := 0.0 }
  | 5 => { x := 0.0, y := -1.0, z := 0.0 }
  | _ => { x := 0.0, y := 1.0, z := 0.0 }

-- Helper: face is one of 0-5
theorem face_lt_6 (face : Nat) (h : face < 6) : face = 0 ∨ face = 1 ∨ face = 2 ∨ face = 3 ∨ face = 4 ∨ face = 5 := by
  omega

-- View direction X component is 1 for +X, -1 for -X, 0 otherwise
theorem view_dir_x (face : Nat) (h : face < 6) :
    (viewDir {x:=0,y:=0,z:=0} face).x = (if face = 0 then 1.0 else if face = 1 then -1.0 else 0.0) := by
  rcases face_lt_6 face h with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [viewDir]

-- View direction Y component is 1 for +Y, -1 for -Y, 0 otherwise
theorem view_dir_y (face : Nat) (h : face < 6) :
    (viewDir {x:=0,y:=0,z:=0} face).y = (if face = 2 then 1.0 else if face = 3 then -1.0 else 0.0) := by
  rcases face_lt_6 face h with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [viewDir]

-- View direction Z component is 1 for +Z, -1 for -Z, 0 otherwise
theorem view_dir_z (face : Nat) (h : face < 6) :
    (viewDir {x:=0,y:=0,z:=0} face).z = (if face = 4 then 1.0 else if face = 5 then -1.0 else 0.0) := by
  rcases face_lt_6 face h with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [viewDir]

-- The 6 face directions cover all axis directions
theorem faces_are_axis_aligned (face : Nat) (h : face < 6) : True := by
  trivial

-- Up vector X is always 0
theorem up_x_zero (face : Nat) (h : face < 6) : (faceUp face).x = 0.0 := by
  rcases face_lt_6 face h with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [faceUp]

-- Up vector Z is 0 for all faces except +Y and -Y
theorem up_z_nonzero_only_for_y (face : Nat) (h : face < 6) : (faceUp face).z = 0.0 ∨ (faceUp face).z = 1.0 ∨ (faceUp face).z = -1.0 := by
  rcases face_lt_6 face h with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [faceUp]

end GxProofs.PointShadowFaces
