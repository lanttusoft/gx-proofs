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
  //ai: componentwise exact-rational residual and camera-column bounds.
  Homogeneous margins and IEEE/GPU uncertainty remain external obligations.
-/
import GxProofsGfx.Temporal.ReprojectionError

namespace GxProofsGfx.WeightedReprojection
open GxMath.ClipMatrix ReprojectionError

def ComponentBound (v b : Vec4) : Prop :=
  |v.x| ≤ b.x ∧ |v.y| ≤ b.y ∧ |v.z| ≤ b.z ∧ |v.w| ≤ b.w

def absolute (v : Vec4) : Vec4 := ⟨|v.x|, |v.y|, |v.z|, |v.w|⟩

def weightedAction (b : Vec4) (m : Mat4) : Vec4 :=
  ⟨b.x*|m.m00|+b.y*|m.m10|+b.z*|m.m20|+b.w*|m.m30|,
   b.x*|m.m01|+b.y*|m.m11|+b.z*|m.m21|+b.w*|m.m31|,
   b.x*|m.m02|+b.y*|m.m12|+b.z*|m.m22|+b.w*|m.m32|,
   b.x*|m.m03|+b.y*|m.m13|+b.z*|m.m23|+b.w*|m.m33|⟩

theorem weighted_dot (a b c d p q r s ax ay cz dw : ℚ)
    (ha : |a| ≤ ax) (hb : |b| ≤ ay) (hc : |c| ≤ cz) (hd : |d| ≤ dw) :
    |a*p+b*q+c*r+d*s| ≤ ax * |p| + ay * |q| + cz * |r| + dw * |s| := by
  have h1 := mul_le_mul_of_nonneg_right ha (abs_nonneg p)
  have h2 := mul_le_mul_of_nonneg_right hb (abs_nonneg q)
  have h3 := mul_le_mul_of_nonneg_right hc (abs_nonneg r)
  have h4 := mul_le_mul_of_nonneg_right hd (abs_nonneg s)
  have t1 := abs_add_le (a*p) (b*q)
  have t2 := abs_add_le (a*p+b*q) (c*r)
  have t3 := abs_add_le (a*p+b*q+c*r) (d*s)
  simp only [abs_mul] at t1 t2 t3
  linarith

theorem weighted_row_bound (v b : Vec4) (m : Mat4) (h : ComponentBound v b) :
    ComponentBound (rowMul v m) (weightedAction b m) :=
  ⟨weighted_dot _ _ _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2,
   weighted_dot _ _ _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2,
   weighted_dot _ _ _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2,
   weighted_dot _ _ _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2⟩

theorem weighted_residual_bound (world : Vec4) (current candidate : Mat4) :
    ComponentBound (vectorSub (rowMul (rowMul world current) candidate) world)
      (weightedAction (absolute world) (residual current candidate)) := by
  rw [residual_action]
  exact weighted_row_bound world (absolute world) _ ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩

def normalizedBudget (world b : Vec4) (mu : ℚ) : Vec4 :=
  ⟨(b.x+|world.x| * b.w)/mu, (b.y+|world.y| * b.w)/mu,
   (b.z+|world.z| * b.w)/mu, 0⟩

theorem normalized_component_bound (world recovered b : Vec4) (mu : ℚ)
    (hmu : 0 < mu) (hd : mu ≤ |recovered.w|) (hw : world.w = 1)
    (h : ComponentBound (vectorSub recovered world) b) :
    ComponentBound (vectorSub (TemporalMatrix.normalize recovered) world) (normalizedBudget world b mu) := by
  have rn : recovered.w ≠ 0 := by intro hz; simp [hz] at hd; linarith
  have coord (a a0 en : ℚ) (hn : |a-a0| ≤ en) :
      |a/recovered.w-a0| ≤ (en+|a0| * b.w)/mu := by
    simpa [ratioBudget] using ratio_perturbation a recovered.w a0 1 mu en b.w
      hmu hd (by norm_num) hn (by simpa [vectorSub, hw] using h.2.2.2)
  refine ⟨?_,?_,?_,?_⟩
  · simpa [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizedBudget, div_eq_mul_inv]
      using coord recovered.x world.x b.x h.1
  · simpa [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizedBudget, div_eq_mul_inv]
      using coord recovered.y world.y b.y h.2.1
  · simpa [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizedBudget, div_eq_mul_inv]
      using coord recovered.z world.z b.z h.2.2.1
  · simp [vectorSub, TemporalMatrix.normalize, TemporalMatrix.scale, normalizedBudget, rn, hw]

def residualBudget (world : Vec4) (current candidate : Mat4) : Vec4 :=
  weightedAction (absolute world) (residual current candidate)

def worldBudget (world : Vec4) (current candidate : Mat4) (mu : ℚ) : Vec4 :=
  normalizedBudget world (residualBudget world current candidate) mu

theorem shader_world_bound (world : Vec4) (current candidate : Mat4) (mu : ℚ)
    (hmu : 0 < mu) (hd : mu ≤ |(rowMul (rowMul world current) candidate).w|)
    (hw : world.w = 1) (hc : (rowMul world current).w ≠ 0) :
    ComponentBound (vectorSub (reconstruct world current candidate) world)
      (worldBudget world current candidate mu) := by
  have hr : (rowMul (rowMul world current) candidate).w ≠ 0 := by
    intro hz; simp [hz] at hd; linarith
  unfold reconstruct
  rw [shader_normalization_equiv world current candidate hc hr]
  exact normalized_component_bound world _ _ mu hmu hd hw
    (weighted_residual_bound world current candidate)

theorem weighted_previous_clip (actual ideal b : Vec4) (previous : Mat4)
    (h : ComponentBound (vectorSub actual ideal) b) :
    ComponentBound (vectorSub (rowMul actual previous) (rowMul ideal previous)) (weightedAction b previous) := by
  have linear : vectorSub (rowMul actual previous) (rowMul ideal previous) =
      rowMul (vectorSub actual ideal) previous := by
    ext <;> simp [vectorSub, rowMul] <;> ring
  rw [linear]
  exact weighted_row_bound _ b previous h

--ai: numerator and denominator bounds remain separate through all three projections.
theorem weighted_previous_projection (world : Vec4) (current candidate previous : Mat4)
    (mu nu : ℚ) (hmu : 0 < mu)
    (hd : mu ≤ |(rowMul (rowMul world current) candidate).w|)
    (hw : world.w = 1) (hc : (rowMul world current).w ≠ 0)
    (hnu : 0 < nu) (hp : nu ≤ |(rowMul (reconstruct world current candidate) previous).w|)
    (hi : (rowMul world previous).w ≠ 0) :
    let actual := rowMul (reconstruct world current candidate) previous
    let ideal := rowMul world previous
    let b := weightedAction (worldBudget world current candidate mu) previous
    |TemporalSampling.project actual.x actual.w-TemporalSampling.project ideal.x ideal.w| ≤ projectionBudget nu b.x b.w (ideal.x/ideal.w) ∧
    |TemporalSampling.project actual.y actual.w-TemporalSampling.project ideal.y ideal.w| ≤ projectionBudget nu b.y b.w (ideal.y/ideal.w) ∧
    |TemporalSampling.project actual.z actual.w-TemporalSampling.project ideal.z ideal.w| ≤ projectionBudget nu b.z b.w (ideal.z/ideal.w) := by
  have h := weighted_previous_clip (reconstruct world current candidate) world _ previous
    (shader_world_bound world current candidate mu hmu hd hw hc)
  exact ⟨projection_perturbation _ _ _ _ _ _ _ hnu hp hi h.1 h.2.2.2,
    projection_perturbation _ _ _ _ _ _ _ hnu hp hi h.2.1 h.2.2.2,
    projection_perturbation _ _ _ _ _ _ _ hnu hp hi h.2.2.1 h.2.2.2⟩

--ai: weighted sums refine the uniform 4WE envelope, without relying on sign cancellation.
theorem weighted_sum_le_uniform (a b c d p q r s w e : ℚ) (hw : 0 ≤ w)
    (hv : |a| ≤ w ∧ |b| ≤ w ∧ |c| ≤ w ∧ |d| ≤ w)
    (hm : |p| ≤ e ∧ |q| ≤ e ∧ |r| ≤ e ∧ |s| ≤ e) :
    |a| * |p| + |b| * |q| + |c| * |r| + |d| * |s| ≤ 4*w*e := by
  have h1 := abs_product_bound a p w e hw hv.1 hm.1
  have h2 := abs_product_bound b q w e hw hv.2.1 hm.2.1
  have h3 := abs_product_bound c r w e hw hv.2.2.1 hm.2.2.1
  have h4 := abs_product_bound d s w e hw hv.2.2.2 hm.2.2.2
  simp only [abs_mul] at h1 h2 h3 h4
  linarith

end GxProofsGfx.WeightedReprojection
