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
  gX — Frustum AABB Culling Specification

  Salvaged from gameX lean/GameXProofs/FrustumCull.lean, re-verified:
  src/renderer/gfx/model.c:503-506 selects the 8 AABB corners
  with the identical bit pattern (i&1 → x max/min, i&2 → y, i&4 → z)
  before the clip-space [-1,1] test in gX_Model_FrustumTest.

  Discrete part (Bool): the 8 bit patterns exist, are distinct, and the
    corner selection reads the right bit per axis.
  Real part (ℝ): every selected corner coordinate lies inside the box
    [aabbMin, aabbMax], and the corner extremes equal the box extremes.

  Theorems proven: 7
    - eight_corners:            allCorners has length 8
    - corners_distinct:         no two bit patterns are equal
    - corner_x_selects_min_max: x-bit selects min vs max
    - corner_y_selects_min_max: y-bit selects min vs max
    - corner_z_selects_min_max: z-bit selects min vs max
    - corner_in_box:            every corner coordinate is within [min, max]
    - corner_extremes:          min/max corners hit the box extremes exactly
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.FrustumCull

-- A 3-bit selection for AABB corners.
structure CornerBits where
  x : Bool
  y : Bool
  z : Bool
deriving DecidableEq

-- A list of all 8 corners.
def allCorners : List CornerBits :=
  [ { x := false, y := false, z := false }
  , { x := true,  y := false, z := false }
  , { x := false, y := true,  z := false }
  , { x := true,  y := true,  z := false }
  , { x := false, y := false, z := true  }
  , { x := true,  y := false, z := true  }
  , { x := false, y := true,  z := true  }
  , { x := true,  y := true,  z := true  }
  ]

theorem eight_corners : allCorners.length = 8 := by
  unfold allCorners; simp

-- No two of the 8 corner bit patterns are equal (each index is unique).
theorem corners_distinct :
    List.Pairwise (fun a b : CornerBits => a ≠ b) allCorners := by
  unfold allCorners
  decide

-- Corner selection: bit selects aabbMin.x when false, aabbMax.x when true.
def cornerX (c : CornerBits) (minX maxX : ℝ) : ℝ :=
  if c.x then maxX else minX

def cornerY (c : CornerBits) (minY maxY : ℝ) : ℝ :=
  if c.y then maxY else minY

def cornerZ (c : CornerBits) (minZ maxZ : ℝ) : ℝ :=
  if c.z then maxZ else minZ

-- x-bit: false picks min, true picks max.
theorem corner_x_selects_min_max (minX maxX : ℝ) :
    cornerX { x := false, y := false, z := false } minX maxX = minX ∧
    cornerX { x := true,  y := false, z := false } minX maxX = maxX := by
  simp [cornerX]

-- y-bit: false picks min, true picks max.
theorem corner_y_selects_min_max (minY maxY : ℝ) :
    cornerY { x := false, y := false, z := false } minY maxY = minY ∧
    cornerY { x := false, y := true,  z := false } minY maxY = maxY := by
  simp [cornerY]

-- z-bit: false picks min, true picks max.
theorem corner_z_selects_min_max (minZ maxZ : ℝ) :
    cornerZ { x := false, y := false, z := false } minZ maxZ = minZ ∧
    cornerZ { x := false, y := false, z := true  } minZ maxZ = maxZ := by
  simp [cornerZ]

-- AABB with min ≤ max componentwise (validity carried as a hypothesis).
structure AABB where
  minX : ℝ
  maxX : ℝ
  minY : ℝ
  maxY : ℝ
  minZ : ℝ
  maxZ : ℝ

-- Every corner of a valid AABB has each coordinate inside [min, max].
theorem corner_in_box (b : AABB) (hvalid : b.minX ≤ b.maxX ∧ b.minY ≤ b.maxY ∧ b.minZ ≤ b.maxZ)
    (c : CornerBits) :
    b.minX ≤ cornerX c b.minX b.maxX ∧ cornerX c b.minX b.maxX ≤ b.maxX ∧
    b.minY ≤ cornerY c b.minY b.maxY ∧ cornerY c b.minY b.maxY ≤ b.maxY ∧
    b.minZ ≤ cornerZ c b.minZ b.maxZ ∧ cornerZ c b.minZ b.maxZ ≤ b.maxZ := by
  rcases c with ⟨bx, bY, bz⟩
  cases bx <;> cases bY <;> cases bz <;> simp [cornerX, cornerY, cornerZ] <;> exact hvalid

-- The min corner (all bits false) equals (minX, minY, minZ); the max corner
-- (all bits true) equals (maxX, maxY, maxZ) — the box extremes are hit.
theorem corner_extremes (b : AABB) :
    cornerX { x := false, y := false, z := false } b.minX b.maxX = b.minX ∧
    cornerY { x := false, y := false, z := false } b.minY b.maxY = b.minY ∧
    cornerZ { x := false, y := false, z := false } b.minZ b.maxZ = b.minZ ∧
    cornerX { x := true, y := true, z := true } b.minX b.maxX = b.maxX ∧
    cornerY { x := true, y := true, z := true } b.minY b.maxY = b.maxY ∧
    cornerZ { x := true, y := true, z := true } b.minZ b.maxZ = b.maxZ := by
  simp [cornerX, cornerY, cornerZ]

end GxProofsGfx.FrustumCull
