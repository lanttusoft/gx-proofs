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
  gX — Independent Diffuse Light Accumulation

  Models the per-light Lambert diffuse term and additive loop in
  resources/shader/standard.frag:500-508,597-653. A light on the
  back-facing side contributes zero; it must not erase contributions from
  other lights. This contract targets the reported two-light PBR regression.

  Theorems proven: 3
    - back_facing_contributes_zero: one back-facing light has zero diffuse term
    - diffuse_sum_append:           accumulation composes over list append
    - back_facing_insertion_neutral: adding a back-facing light anywhere leaves
                                     all other diffuse contributions unchanged

  This mathematical contract complements renderer integration captures; it
  does not establish that the GLSL loop executes or uploads every light.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.LightAccumulation

--opencode: keep a back-facing diffuse term neutral to the other light terms.
def diffuseContribution (weight nDotL : ℝ) : ℝ :=
  weight * max nDotL 0

def diffuseSum (lights : List (ℝ × ℝ)) : ℝ :=
  (lights.map fun light => diffuseContribution light.1 light.2).sum

theorem back_facing_contributes_zero (weight nDotL : ℝ) (hBack : nDotL ≤ 0) :
    diffuseContribution weight nDotL = 0 := by
  unfold diffuseContribution
  rw [max_eq_right hBack]
  simp

theorem diffuse_sum_append (first second : List (ℝ × ℝ)) :
    diffuseSum (first ++ second) = diffuseSum first + diffuseSum second := by
  simp [diffuseSum, List.map_append, List.sum_append]

theorem back_facing_insertion_neutral
    (before after : List (ℝ × ℝ)) (weight nDotL : ℝ) (hBack : nDotL ≤ 0) :
    diffuseSum (before ++ (weight, nDotL) :: after) =
      diffuseSum (before ++ after) := by
  rw [diffuse_sum_append, diffuse_sum_append]
  simp [diffuseSum, back_facing_contributes_zero weight nDotL hBack]

end GxProofsGfx.LightAccumulation
