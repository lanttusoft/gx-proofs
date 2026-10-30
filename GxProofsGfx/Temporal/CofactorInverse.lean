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
  //ai: camera-history bridge for the generic GxMath cofactor inverse.
  The exact algebra, minors, determinant, adjugate and inverse contracts live
  in GxMath.CofactorInverse. This module keeps only the GFX-specific
  reconstruction theorem that composes the inverse with the temporal
  upload/normalization path.
-/
import GxMath.CofactorInverse
import GxProofsGfx.Temporal.TemporalMatrix

namespace GxProofsGfx.CofactorInverse
open GxMath.ClipMatrix
open GxMath.CofactorInverse
open GxProofsGfx.TemporalMatrix

--ai: replaces the previous abstract inverse hypothesis by the source-grounded nonzero determinant contract.
theorem camera_reconstruction (current : Mat4) (world : Vec4)
    (hd : determinant current ≠ 0) (hw : world.w = 1)
    (hc : (rowMul world current).w ≠ 0) :
    normalize (colMul (upload true (inverse current))
      (normalize (rowMul world current))) = world :=
  ideal_world_reconstruction current (inverse current) world
    (inverse_product_right current hd) hw hc

end GxProofsGfx.CofactorInverse
