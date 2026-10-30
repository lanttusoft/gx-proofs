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
  gxmath/Vector64.lean
  gX — a game engine

  Formal contract for gX_F64v4_Lerp in src/gxmath/vector4.c.
  The C type is a four-component double vector; the formal model is over ℝ
  and does not certify IEEE-754 execution.

  Theorems proven:
    - endpoint identities at t = 0 and t = 1
    - fixed-point behavior when both inputs agree
    - componentwise affine form
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxMath
namespace Vector64

@[ext]
structure F64v4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

def lerp (a b : F64v4) (t : ℝ) : F64v4 :=
  { x := a.x + t * (b.x - a.x)
    y := a.y + t * (b.y - a.y)
    z := a.z + t * (b.z - a.z)
    w := a.w + t * (b.w - a.w) }

theorem lerp_zero (a b : F64v4) : lerp a b 0 = a := by
  ext <;> simp [lerp]

theorem lerp_one (a b : F64v4) : lerp a b 1 = b := by
  ext <;> simp [lerp]

theorem lerp_self (a : F64v4) (t : ℝ) : lerp a a t = a := by
  ext <;> simp [lerp]

theorem lerp_eq_affine (a b : F64v4) (t : ℝ) :
    lerp a b t = { x := a.x + t * (b.x - a.x)
                   y := a.y + t * (b.y - a.y)
                   z := a.z + t * (b.z - a.z)
                   w := a.w + t * (b.w - a.w) } := by
  rfl

end Vector64
end GxMath
