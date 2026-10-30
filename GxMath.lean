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

-- Root module for the `GxMath` library (gxmath foundation specs).
import GxMath.Vector
import GxMath.Matrix
--ai: generic clip and cofactor/inverse models moved from the GFX tier.
import GxMath.ClipMatrix
import GxMath.CofactorInverse
--ai: quaternion algebra, norm and inverse contracts.
import GxMath.Quaternion
--ai: signed-distance primitive contracts.
import GxMath.Sdf
--ai: scalar clamp/lerp/normalize/remap contracts.
import GxMath.Scalar
--ai: DFT linearity and impulse contracts.
import GxMath.Fourier
--ai: finite-difference and Newton-step contracts.
import GxMath.Calculus
--ai: signed channel quantization and basic unit conversion contracts.
import GxMath.Color
import GxMath.Units
--ai: exact Cartesian sky-frame round trips, norms and handedness.
import GxMath.Sky
--ai: branch-aware cylindrical/spherical coordinate contracts.
import GxMath.Coordinates
--ai: Include the small-matrix determinant/trace and F64v4 contracts in the foundation gate.
import GxMath.MatrixSmall
import GxMath.Vector64
--ai: generic easing contracts moved out of the GFX tier.
import GxMath.Easing
--ai: Include the normal-matrix contract in the Mathlib foundation gate.
import GxMath.NormalMatrix
--ai: Include the SI physics contracts (EM + thermal radiation) in the gate.
import GxMath.Physics
