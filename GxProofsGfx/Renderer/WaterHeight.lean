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
  //ai: conditional exact-real contract for the bounded world-space water query.

  The C query uses the fixed-point update parameter := world - horizontalOffset(parameter).
  Under a global contraction hypothesis, Banach iteration converges to the unique
  inverse parameter. Mathlib supplies the finite-iterate error bound; a Lipschitz
  vertical-height map transfers it to an output-height bound after twelve steps.

  The theorems do not establish a contraction constant for arbitrary authored waves,
  float/GLSL correspondence, convergence of the finite C calculation, or equality
  with tessellated triangle interpolation. Source and native probes guard the model.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

namespace GxProofsGfx.WaterHeight
open NNReal Topology Filter Function

abbrev Plane := ℝ × ℝ

def parameterStep (world : Plane) (horizontalOffset : Plane → Plane)
    (parameter : Plane) : Plane :=
  world - horizontalOffset parameter

theorem query_iterates_converge (world : Plane) (horizontalOffset : Plane → Plane)
    (K : ℝ≥0) (seed : Plane)
    (hcontract : ContractingWith K (parameterStep world horizontalOffset)) :
    Tendsto
      (fun n : ℕ => (parameterStep world horizontalOffset)^[n] seed)
      atTop
      (𝓝 (hcontract.fixedPoint (parameterStep world horizontalOffset))) := by
  exact hcontract.tendsto_iterate_fixedPoint seed

theorem query_12_parameter_error (world : Plane) (horizontalOffset : Plane → Plane)
    (K : ℝ≥0) (seed : Plane)
    (hcontract : ContractingWith K (parameterStep world horizontalOffset)) :
    dist
        ((parameterStep world horizontalOffset)^[12] seed)
        (hcontract.fixedPoint (parameterStep world horizontalOffset))
      ≤ dist seed (parameterStep world horizontalOffset seed)
          * (K : ℝ) ^ 12 / (1 - (K : ℝ)) := by
  exact hcontract.apriori_dist_iterate_fixedPoint_le seed 12

theorem query_12_height_error (world : Plane) (horizontalOffset : Plane → Plane)
    (height : Plane → ℝ) (heightLip : ℝ) (K : ℝ≥0) (seed : Plane)
    (hheightLip : ∀ a b, |height a - height b| ≤ heightLip * dist a b)
    (hheightLipNonneg : 0 ≤ heightLip)
    (hcontract : ContractingWith K (parameterStep world horizontalOffset)) :
    |height ((parameterStep world horizontalOffset)^[12] seed)
        - height (hcontract.fixedPoint (parameterStep world horizontalOffset))|
      ≤ heightLip
          * (dist seed (parameterStep world horizontalOffset seed)
              * (K : ℝ) ^ 12 / (1 - (K : ℝ))) := by
  calc
    _ ≤ heightLip
        * dist ((parameterStep world horizontalOffset)^[12] seed)
            (hcontract.fixedPoint (parameterStep world horizontalOffset)) :=
      hheightLip _ _
    _ ≤ heightLip
        * (dist seed (parameterStep world horizontalOffset seed)
            * (K : ℝ) ^ 12 / (1 - (K : ℝ))) :=
      mul_le_mul_of_nonneg_left (query_12_parameter_error world horizontalOffset K seed hcontract)
        hheightLipNonneg

end GxProofsGfx.WaterHeight
