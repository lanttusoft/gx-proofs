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
  //ai: SSGI tangent eligibility and normalize-before-fallback contracts.
  Sampling accuracy, texture filtering, radiance provenance and GPU execution external.
-/
import GxProofsGfx.Postprocess.GtaoContracts

namespace GxProofsGfx.SsgiContracts
open GxMath.ClipMatrix PlanarReflection

def tangent (offset normal : Vec4) : Vec4 :=
  ReflectionHandedness.difference offset (TemporalMatrix.scale normal (dot offset normal))

theorem projected_tangent_orthogonal (offset normal : Vec4) (hn : dot normal normal = 1) :
    dot (tangent offset normal) normal = 0 := by
  simp only [tangent,ReflectionHandedness.difference,TemporalMatrix.scale,dot] at *
  linear_combination -(offset.x*normal.x+offset.y*normal.y+offset.z*normal.z)*hn

theorem scaled_tangent_test_still_zero (offset normal : Vec4) (k : ℚ)
    (hn : dot normal normal = 1) : dot (TemporalMatrix.scale (tangent offset normal) k) normal = 0 := by
  have h := projected_tangent_orthogonal offset normal hn
  simp only [TemporalMatrix.scale,dot] at *
  linear_combination k*h

--ai: valid reconstructed hemisphere remains distinct from the deleted always-zero tangent predicate.
theorem tangent_sign_rounding_sensitive : ¬ (0 : ℚ) < 0 ∧ -(1/1000000 : ℚ) < 0 := by norm_num

def estimate (sum count : ℚ) : ℚ := sum/count
def fallback (ambient sum count confidence : ℚ) : ℚ :=
  CsmContracts.mix ambient (estimate sum count) confidence

theorem normalize_before_fallback (ambient sum count confidence : ℚ) (hn : count ≠ 0) :
    fallback ambient sum count confidence = (1-confidence)*ambient+confidence*sum/count := by
  unfold fallback estimate CsmContracts.mix
  field_simp

theorem ambient_matching_estimate_stable (ambient count confidence : ℚ) (hn : count ≠ 0) :
    fallback ambient (ambient*count) count confidence = ambient := by
  unfold fallback estimate CsmContracts.mix
  field_simp
  ring

theorem old_fallback_count_negative :
    CsmContracts.mix (1 : ℚ) 2 (2/48)/2 ≠ fallback 1 2 2 (2/48) := by
  norm_num [fallback,estimate,CsmContracts.mix]

theorem two_sided_candidate_budget : 4*6*2 = (48 : ℕ) := by norm_num

theorem confidence_range (count : ℚ) (hl : 0 ≤ count) (hu : count ≤ 48) :
    0 ≤ count/48 ∧ count/48 ≤ 1 := by constructor <;> linarith

theorem nonnegative_estimate (sum count : ℚ) (hs : 0 ≤ sum) (hc : 0 < count) :
    0 ≤ estimate sum count := div_nonneg hs (le_of_lt hc)

theorem conditional_radiance_bound (sum count cap : ℚ) (hc : 0 < count)
    (hs : sum ≤ count*cap) : estimate sum count ≤ cap := by
  unfold estimate
  rw [div_le_iff₀ hc]
  nlinarith

end GxProofsGfx.SsgiContracts
