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
  gxmath/Quaternion.lean
  gX — a game engine

  Formal contracts for gX_F32Qua algebra in src/gxmath/quaternion.c.
  The C type is a four-component float vector used as (x,y,z,w); the formal
  model is over ℝ. The 0.95 Slerp branch is represented by exact 19/20 and
  the zero-sine threshold is an explicit parameter; IEEE comparisons,
  transcendental accuracy and float normalization remain outside this module.
  //ai: the native vector helper is homogeneous q*v*conj(q); its length
  scales by normSq(q). Native ToMatrix has literal-one diagonal terms and
  agrees with vector rotation only for exact unit quaternions. Matrices use
  the existing GxMath.Matrix transform convention. No IEEE normalization,
  inverse-conditioning, GPU upload or slerp/nlerp branch accuracy is certified.

  Theorems proven:
    - identity multiplication
    - norm-squared multiplicativity and non-negativity
    - conjugate involution and norm preservation
    - q * conj(q) = normSq(q) * identity
    - left/right inverse identities under nonzero norm
    - inverse norm scaling
    - //ai: branch-aware Lerp/Nlerp/Slerp models, endpoint/zero cases and exact regular-path norm
    - //ai: rotation/sandwich, unit norm, antipodal sign, composition and inverse action
    - //ai: unit-only matrix agreement, nonunit scaling law and explicit counterexample
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
--ai: reuse the established engine vector/matrix transform model, without changing its convention.
import GxMath.Matrix

namespace GxMath
namespace Quaternion

@[ext]
structure Qua where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

def one : Qua :=
  { x := 0, y := 0, z := 0, w := 1 }

def mul (a b : Qua) : Qua :=
  { x := a.x * b.w + a.w * b.x + a.y * b.z - a.z * b.y
    y := a.y * b.w + a.w * b.y + a.z * b.x - a.x * b.z
    z := a.z * b.w + a.w * b.z + a.x * b.y - a.y * b.x
    w := a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z }

def conj (q : Qua) : Qua :=
  { x := -q.x, y := -q.y, z := -q.z, w := q.w }

def normSq (q : Qua) : ℝ :=
  q.x ^ 2 + q.y ^ 2 + q.z ^ 2 + q.w ^ 2

noncomputable def norm (q : Qua) : ℝ :=
  Real.sqrt (normSq q)

def scale (q : Qua) (s : ℝ) : Qua :=
  { x := q.x * s, y := q.y * s, z := q.z * s, w := q.w * s }

noncomputable def inv (q : Qua) : Qua :=
  { x := -q.x / normSq q
    y := -q.y / normSq q
    z := -q.z / normSq q
    w := q.w / normSq q }

theorem one_mul (q : Qua) : mul one q = q := by
  ext <;> simp [mul, one]

theorem mul_one (q : Qua) : mul q one = q := by
  ext <;> simp [mul, one]

theorem normSq_nonneg (q : Qua) : 0 ≤ normSq q := by
  unfold normSq
  nlinarith [sq_nonneg q.x, sq_nonneg q.y, sq_nonneg q.z, sq_nonneg q.w]

theorem normSq_one : normSq one = 1 := by
  norm_num [normSq, one]

theorem conj_conj (q : Qua) : conj (conj q) = q := by
  ext <;> simp [conj]

theorem normSq_conj (q : Qua) : normSq (conj q) = normSq q := by
  simp [normSq, conj]

theorem normSq_mul (a b : Qua) :
    normSq (mul a b) = normSq a * normSq b := by
  simp [normSq, mul]
  ring

theorem mul_conj (q : Qua) :
    mul q (conj q) = scale one (normSq q) := by
  ext <;> simp [mul, conj, scale, one, normSq] <;> ring

theorem inv_one : inv one = one := by
  ext <;> norm_num [inv, normSq, one]

theorem mul_inv (q : Qua) (h : normSq q ≠ 0) :
    mul q (inv q) = one := by
  have hs : q.w ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≠ 0 := by
    simpa [normSq, add_assoc, add_comm, add_left_comm] using h
  ext <;> simp [mul, inv, one] <;> field_simp [h] <;> simp [normSq] <;> ring

theorem inv_mul (q : Qua) (h : normSq q ≠ 0) :
    mul (inv q) q = one := by
  have hs : q.w ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≠ 0 := by
    simpa [normSq, add_assoc, add_comm, add_left_comm] using h
  ext <;> simp [mul, inv, one] <;> field_simp [h] <;> simp [normSq] <;> ring

theorem normSq_inv (q : Qua) (h : normSq q ≠ 0) :
    normSq (inv q) = 1 / normSq q := by
  have hs : q.w ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≠ 0 := by
    simpa [normSq, add_assoc, add_comm, add_left_comm] using h
  simp [normSq, inv]
  field_simp [hs]

--ai: exact-real coordinate model of the native quaternion dot product.
def dot (a b : Qua) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w

--ai: zero and sign-flip values used by interpolation's explicit antipodal handling.
def zero : Qua := { x := 0, y := 0, z := 0, w := 0 }

--ai: componentwise quaternion negation mirrors the C sign correction.
def neg (q : Qua) : Qua := { x := -q.x, y := -q.y, z := -q.z, w := -q.w }

--ai: C's interpolation is q1 + t*(q2-q1), preserved componentwise over ℝ.
def lerpQua (q1 q2 : Qua) (t : ℝ) : Qua :=
  { x := q1.x + t * (q2.x - q1.x)
    y := q1.y + t * (q2.y - q1.y)
    z := q1.z + t * (q2.z - q1.z)
    w := q1.w + t * (q2.w - q1.w) }

--ai: exact-real counterpart of C Normalize, including its zero-length no-op branch.
noncomputable def normalize (q : Qua) : Qua :=
  if normSq q = 0 then q else scale q (1 / norm q)

--ai: native Nlerp is Lerp followed by the zero-aware quaternion normalizer.
noncomputable def nlerp (q1 q2 : Qua) (t : ℝ) : Qua := normalize (lerpQua q1 q2 t)

--ai: weighted sum used by the exact spherical interpolation formula.
def weighted (q1 : Qua) (a : ℝ) (q2 : Qua) (b : ℝ) : Qua :=
  { x := q1.x * a + q2.x * b
    y := q1.y * a + q2.y * b
    z := q1.z * a + q2.z * b
    w := q1.w * a + q2.w * b }

--ai: exact-real regular Slerp formula, with C's sqrt(1-c^2) denominator.
noncomputable def slerpRegular (q1 q2 : Qua) (c t : ℝ) : Qua :=
  let sinHalf := Real.sqrt (1 - c ^ 2)
  weighted q1 (Real.sin ((1 - t) * Real.arccos c) / sinHalf)
    q2 (Real.sin (t * Real.arccos c) / sinHalf)

--ai: exact-real branch model of gX_F32Qua_Slerp; 0.95f is idealized as 19/20 and epsilon is explicit.
noncomputable def slerp (q1 q2 : Qua) (t epsilon : ℝ) : Qua :=
  let cosine := dot q1 q2
  let q2Adjusted := if cosine < 0 then neg q2 else q2
  let cosineAdjusted := if cosine < 0 then -cosine else cosine
  if |cosineAdjusted| >= 1 then q1
  else if cosineAdjusted > 19 / 20 then nlerp q1 q2Adjusted t
  else
    let sinHalf := Real.sqrt (1 - cosineAdjusted ^ 2)
    if |sinHalf| < epsilon then lerpQua q1 q2Adjusted (1 / 2)
    else slerpRegular q1 q2Adjusted cosineAdjusted t

--ai: scalar multiplication scales the exact squared quaternion length quadratically.
theorem normSq_scale (q : Qua) (s : ℝ) : normSq (scale q s) = normSq q * s ^ 2 := by
  simp [normSq, scale]
  ring

--ai: sign reversal preserves squared length.
theorem normSq_neg (q : Qua) : normSq (neg q) = normSq q := by
  simp [normSq, neg]

--ai: the real normalizer produces unit squared length exactly when its input is nonzero.
theorem normSq_normalize_of_ne_zero (q : Qua) (h : normSq q ≠ 0) :
    normSq (normalize q) = 1 := by
  have hpos : 0 < normSq q := lt_of_le_of_ne (normSq_nonneg q) (Ne.symm h)
  have hsqrt : Real.sqrt (normSq q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  rw [normalize, if_neg h, normSq_scale]
  change normSq q * (1 / Real.sqrt (normSq q)) ^ 2 = 1
  have hsquare := Real.sq_sqrt (normSq_nonneg q)
  field_simp [hsqrt]
  nlinarith

--ai: nlerp has unit squared length unless the native linear blend is zero.
theorem normSq_nlerp_of_lerp_ne_zero (q1 q2 : Qua) (t : ℝ)
    (h : normSq (lerpQua q1 q2 t) ≠ 0) : normSq (nlerp q1 q2 t) = 1 :=
  normSq_normalize_of_ne_zero _ h

--ai: Lerp endpoint identities are exact for every real interpolation amount.
theorem lerpQua_zero (q1 q2 : Qua) : lerpQua q1 q2 0 = q1 := by
  ext <;> simp [lerpQua]

--ai: the other Lerp endpoint is the second quaternion.
theorem lerpQua_one (q1 q2 : Qua) : lerpQua q1 q2 1 = q2 := by
  ext <;> simp [lerpQua]

--ai: unit endpoints survive Nlerp's normalization at the exact endpoints.
theorem nlerp_zero (q1 q2 : Qua) (h : normSq q1 = 1) : nlerp q1 q2 0 = q1 := by
  simp [nlerp, lerpQua, normalize, norm, scale, h]

--ai: the second unit endpoint survives Nlerp normalization too.
theorem nlerp_one (q1 q2 : Qua) (h : normSq q2 = 1) : nlerp q1 q2 1 = q2 := by
  simp [nlerp, lerpQua, normalize, norm, scale, h]

--ai: antipodal Nlerp at the midpoint hits zero, and C's zero-normalize branch returns zero.
theorem nlerp_antipodal_midpoint (q : Qua) :
    nlerp q (neg q) (1 / 2) = zero := by
  have hlerp : lerpQua q (neg q) (1 / 2) = zero := by
    ext <;> simp [lerpQua, neg, zero] <;> ring
  rw [nlerp, hlerp]
  simp [normalize, normSq, zero]

--ai: the scalar sine identity underlying exact spherical interpolation norm preservation.
theorem sin_pair_identity (a b : ℝ) :
    Real.sin a ^ 2 + Real.sin b ^ 2 +
      2 * Real.cos (a + b) * Real.sin a * Real.sin b = Real.sin (a + b) ^ 2 := by
  rw [Real.sin_add, Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

--ai: exact spherical weights have squared norm one when divided by nonzero sin(theta).
theorem slerp_sine_weights (theta t : ℝ) (h : Real.sin theta ≠ 0) :
    (Real.sin ((1 - t) * theta) / Real.sin theta) ^ 2 +
      (Real.sin (t * theta) / Real.sin theta) ^ 2 +
      2 * Real.cos theta *
        (Real.sin ((1 - t) * theta) / Real.sin theta) *
        (Real.sin (t * theta) / Real.sin theta) = 1 := by
  have hsum : (1 - t) * theta + t * theta = theta := by ring
  have hid := sin_pair_identity ((1 - t) * theta) (t * theta)
  rw [hsum] at hid
  field_simp [h]
  nlinarith

--ai: squared norm of a two-quaternion weighted sum includes their dot cross-term.
theorem normSq_weighted (q1 q2 : Qua) (a b : ℝ) :
    normSq (weighted q1 a q2 b) =
      a ^ 2 * normSq q1 + b ^ 2 * normSq q2 + 2 * a * b * dot q1 q2 := by
  simp [normSq, weighted, dot]
  ring

--ai: the regular analytic Slerp path preserves unit norm under the exact cosine relation.
theorem slerpRegular_unit (q1 q2 : Qua) (c t : ℝ)
    (h1 : normSq q1 = 1) (h2 : normSq q2 = 1)
    (hdot : dot q1 q2 = c) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    normSq (slerpRegular q1 q2 c t) = 1 := by
  have hc_lower : -1 ≤ c := by linarith
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hc_lower hc1.le
  have hradicand : 0 < 1 - c ^ 2 := by nlinarith
  have hden : Real.sqrt (1 - c ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hradicand)
  have hsin : Real.sin (Real.arccos c) = Real.sqrt (1 - c ^ 2) := Real.sin_arccos c
  have hsin_ne : Real.sin (Real.arccos c) ≠ 0 := by rw [hsin]; exact hden
  have hweights := slerp_sine_weights (Real.arccos c) t hsin_ne
  rw [hcos, hsin] at hweights
  rw [slerpRegular, normSq_weighted, h1, h2, hdot]
  nlinarith [hweights]

--ai: exact regular Slerp starts at its first endpoint; the assumptions exclude a singular denominator.
theorem slerpRegular_zero (q1 q2 : Qua) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    slerpRegular q1 q2 c 0 = q1 := by
  have hradicand : 0 < 1 - c ^ 2 := by nlinarith
  have hden : Real.sqrt (1 - c ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hradicand)
  have hratio : Real.sin (Real.arccos c) / Real.sqrt (1 - c ^ 2) = 1 := by
    rw [Real.sin_arccos]
    exact div_self hden
  simp [slerpRegular, hratio, weighted]

--ai: exact regular Slerp ends at its second endpoint under the same nonsingular domain.
theorem slerpRegular_one (q1 q2 : Qua) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    slerpRegular q1 q2 c 1 = q2 := by
  have hradicand : 0 < 1 - c ^ 2 := by nlinarith
  have hden : Real.sqrt (1 - c ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hradicand)
  have hratio : Real.sin (Real.arccos c) / Real.sqrt (1 - c ^ 2) = 1 := by
    rw [Real.sin_arccos]
    exact div_self hden
  simp [slerpRegular, hratio, weighted]

--ai: Slerp's first branch preserves an identical unit quaternion for every amount.
theorem slerp_same_unit (q : Qua) (t epsilon : ℝ) (h : normSq q = 1) :
    slerp q q t epsilon = q := by
  have hdot : dot q q = 1 := by
    calc
      dot q q = normSq q := by simp [dot, normSq]; ring
      _ = 1 := h
  simp [slerp, hdot]
  all_goals norm_num

--ai: sign-corrected Slerp maps unit antipodal endpoints to the first quaternion.
theorem slerp_antipodal_unit (q : Qua) (t epsilon : ℝ) (h : normSq q = 1) :
    slerp q (neg q) t epsilon = q := by
  have hdot : dot q (neg q) = -1 := by
    have hdot' : dot q (neg q) = -normSq q := by simp [dot, neg, normSq]; ring
    rw [hdot', h]
  simp [slerp, hdot]

--ai: the strict near-parallel threshold selects Nlerp in the exact branch model.
theorem slerp_near_branch (q1 q2 : Qua) (t epsilon : ℝ)
    (hl : 19 / 20 < dot q1 q2) (hu : dot q1 q2 < 1) :
    slerp q1 q2 t epsilon = nlerp q1 q2 t := by
  have hpos : 0 < dot q1 q2 := by linarith
  have hnotneg : ¬ dot q1 q2 < 0 := not_lt.mpr hpos.le
  simp [slerp, hnotneg, abs_of_pos hpos, hl, hu]

--ai: the near-parallel branch inherits Nlerp's exact unit result when its blend is nonzero.
theorem slerp_near_unit (q1 q2 : Qua) (t epsilon : ℝ)
    (hl : 19 / 20 < dot q1 q2) (hu : dot q1 q2 < 1)
    (hblend : normSq (lerpQua q1 q2 t) ≠ 0) :
    normSq (slerp q1 q2 t epsilon) = 1 := by
  rw [slerp_near_branch q1 q2 t epsilon hl hu]
  exact normSq_nlerp_of_lerp_ne_zero q1 q2 t hblend

--ai: the exact regular Slerp branch is selected on the closed [0,19/20] cosine interval when the epsilon guard permits it.
theorem slerp_regular_branch (q1 q2 : Qua) (c t epsilon : ℝ)
    (hdot : dot q1 q2 = c) (hc0 : 0 ≤ c) (hc_hi : c ≤ 19 / 20)
    (hepsilon : epsilon ≤ Real.sqrt (1 - c ^ 2)) :
    slerp q1 q2 t epsilon = slerpRegular q1 q2 c t := by
  have hc_lt : c < 1 := by linarith
  have hnotneg : ¬ c < 0 := not_lt.mpr hc0
  have hc_abs : |c| = c := abs_of_nonneg hc0
  have hnotone : ¬ 1 ≤ c := not_le.mpr hc_lt
  have hnotnear : ¬ c > 19 / 20 := not_lt.mpr hc_hi
  have hsin_nonneg : 0 ≤ Real.sqrt (1 - c ^ 2) := Real.sqrt_nonneg _
  have hnotepsilon : ¬ |Real.sqrt (1 - c ^ 2)| < epsilon := by
    rw [abs_of_nonneg hsin_nonneg]
    exact not_lt.mpr hepsilon
  simp [slerp, hdot, hnotneg, hc_abs, hnotone, hnotnear, hnotepsilon]

--ai: composing regular-branch selection with the sine identity proves exact unit output.
theorem slerp_regular_branch_unit (q1 q2 : Qua) (c t epsilon : ℝ)
    (h1 : normSq q1 = 1) (h2 : normSq q2 = 1) (hdot : dot q1 q2 = c)
    (hc0 : 0 ≤ c) (hc_hi : c ≤ 19 / 20)
    (hepsilon : epsilon ≤ Real.sqrt (1 - c ^ 2)) :
    normSq (slerp q1 q2 t epsilon) = 1 := by
  rw [slerp_regular_branch q1 q2 c t epsilon hdot hc0 hc_hi hepsilon]
  exact slerpRegular_unit q1 q2 c t h1 h2 hdot hc0 (by linarith [hc_hi])

--ai: the regular branch's half-sine has a uniform lower bound on its cosine interval.
theorem slerp_sinHalf_lower_bound (c : ℝ) (hc0 : 0 ≤ c) (hc_hi : c ≤ 19 / 20) :
    Real.sqrt (39 / 400) ≤ Real.sqrt (1 - c ^ 2) := by
  have hsq : c ^ 2 ≤ (19 / 20 : ℝ) ^ 2 :=
    (sq_le_sq₀ hc0 (by norm_num : 0 ≤ (19 / 20 : ℝ))).2 hc_hi
  apply Real.sqrt_le_sqrt
  nlinarith [hsq]

--ai: 1e-6 is below that bound, so the defensive small-sine fallback is unreachable in exact regular inputs.
theorem slerp_source_epsilon_below_bound :
    (1 / 1000000 : ℝ) < Real.sqrt (39 / 400) := by
  have hbound : (1 / 100 : ℝ) < Real.sqrt (39 / 400) := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39 / 400)]
    norm_num
  have hsmall : (1 / 1000000 : ℝ) < 1 / 100 := by norm_num
  exact hsmall.trans hbound

--ai: the C epsilon idealization cannot take Slerp's midpoint fallback in its regular cosine interval.
theorem slerp_source_epsilon_regular_guard (c epsilon : ℝ)
    (hc0 : 0 ≤ c) (hc_hi : c ≤ 19 / 20)
    (hepsilon : epsilon ≤ 1 / 1000000) :
    epsilon ≤ Real.sqrt (1 - c ^ 2) := by
  have hbound := slerp_sinHalf_lower_bound c hc0 hc_hi
  have hsource := slerp_source_epsilon_below_bound
  linarith

--ai: Slerp's small-sine guard returns the native arithmetic midpoint, without normalization.
theorem slerp_epsilon_fallback (q1 q2 : Qua) (c t epsilon : ℝ)
    (hdot : dot q1 q2 = c) (hc0 : 0 ≤ c) (hc_hi : c ≤ 19 / 20)
    (hepsilon : Real.sqrt (1 - c ^ 2) < epsilon) :
    slerp q1 q2 t epsilon = lerpQua q1 q2 (1 / 2) := by
  have hc_lt : c < 1 := by linarith
  have hnotneg : ¬ c < 0 := not_lt.mpr hc0
  have hc_abs : |c| = c := abs_of_nonneg hc0
  have hnotone : ¬ 1 ≤ c := not_le.mpr hc_lt
  have hnotnear : ¬ c > 19 / 20 := not_lt.mpr hc_hi
  have hsin_nonneg : 0 ≤ Real.sqrt (1 - c ^ 2) := Real.sqrt_nonneg _
  have hsmall : |Real.sqrt (1 - c ^ 2)| < epsilon := by
    rw [abs_of_nonneg hsin_nonneg]
    exact hepsilon
  simp [slerp, hdot, hnotneg, hc_abs, hnotone, hnotnear, hsmall]

--ai: pure quaternion embedding for the sandwich-product rotation contract.
def pure (v : F32v3) : Qua := { x := v.x, y := v.y, z := v.z, w := 0 }

--ai: exact polynomial in gX_F32v3_RotateByQuaternion; no implicit normalization.
def rotate (q : Qua) (v : F32v3) : F32v3 :=
  { x := v.x * (q.x * q.x + q.w * q.w - q.y * q.y - q.z * q.z) +
      v.y * (2 * q.x * q.y - 2 * q.w * q.z) + v.z * (2 * q.x * q.z + 2 * q.w * q.y)
    y := v.x * (2 * q.w * q.z + 2 * q.x * q.y) +
      v.y * (q.w * q.w - q.x * q.x + q.y * q.y - q.z * q.z) + v.z * (-2 * q.w * q.x + 2 * q.y * q.z)
    z := v.x * (-2 * q.w * q.y + 2 * q.x * q.z) +
      v.y * (2 * q.w * q.x + 2 * q.y * q.z) + v.z * (q.w * q.w - q.x * q.x - q.y * q.y + q.z * q.z) }

--ai: mirror gX_F32Qua_ToMatrix's numeric fields, not physical C struct order.
def toMatrix (q : Qua) : Matrix :=
  { Matrix.identity with
    m0 := 1 - 2 * (q.y * q.y + q.z * q.z)
    m1 := 2 * (q.x * q.y + q.w * q.z)
    m2 := 2 * (q.x * q.z - q.w * q.y)
    m4 := 2 * (q.x * q.y - q.w * q.z)
    m5 := 1 - 2 * (q.x * q.x + q.z * q.z)
    m6 := 2 * (q.y * q.z + q.w * q.x)
    m8 := 2 * (q.x * q.z + q.w * q.y)
    m9 := 2 * (q.y * q.z - q.w * q.x)
    m10 := 1 - 2 * (q.x * q.x + q.y * q.y) }

--ai: native vector rotation is q * pure(v) * conj(q), not the opposite product.
theorem rotate_sandwich (q : Qua) (v : F32v3) :
    pure (rotate q v) = mul (mul q (pure v)) (conj q) := by
  ext <;> simp [pure, rotate, mul, conj] <;> ring

--ai: the identity quaternion leaves every vector unchanged.
theorem rotate_one (v : F32v3) : rotate one v = v := by
  ext <;> simp [rotate, one]

--ai: a scaled quaternion scales the output by the square of the supplied scalar.
theorem rotate_scale (q : Qua) (s : ℝ) (v : F32v3) :
    rotate (scale q s) v = (rotate q v).scale (s ^ 2) := by
  ext <;> simp [rotate, scale, F32v3.scale] <;> ring

--ai: antipodal quaternions have identical vector action without a unit assumption.
theorem rotate_neg (q : Qua) (v : F32v3) : rotate (scale q (-1)) v = rotate q v := by
  rw [rotate_scale]
  ext <;> simp [F32v3.scale]

--ai: record the full nonunit scaling law before specializing to rotations.
theorem rotate_lengthSqr (q : Qua) (v : F32v3) :
    (rotate q v).lengthSqr = normSq q ^ 2 * v.lengthSqr := by
  simp only [rotate, F32v3.lengthSqr, normSq]
  ring

--ai: the homogeneous helper scales length by normSq(q), not by norm(q).
theorem rotate_length (q : Qua) (v : F32v3) :
    (rotate q v).length = normSq q * v.length := by
  apply (sq_eq_sq₀ (F32v3.length_nonneg _) (mul_nonneg (normSq_nonneg q) (F32v3.length_nonneg v))).mp
  rw [F32v3.length_sq, rotate_lengthSqr, mul_pow, F32v3.length_sq]

--ai: exact unit length is a hypothesis, not a float normalization accuracy claim.
theorem rotate_lengthSqr_unit (q : Qua) (v : F32v3) (h : normSq q = 1) :
    (rotate q v).lengthSqr = v.lengthSqr := by
  rw [rotate_lengthSqr, h]
  simp

--ai: unit-quaternion action preserves the exact square-root vector length.
theorem rotate_length_unit (q : Qua) (v : F32v3) (h : normSq q = 1) :
    (rotate q v).length = v.length := by
  rw [rotate_length, h, _root_.one_mul]

--ai: composition order agrees with the native quaternion product: apply b, then a.
theorem rotate_comp (a b : Qua) (v : F32v3) :
    rotate a (rotate b v) = rotate (mul a b) v := by
  ext <;> simp only [rotate, mul] <;> ring

--ai: inverse action restores a vector whenever the quaternion norm is nonzero.
theorem rotate_inv_left (q : Qua) (v : F32v3) (h : normSq q ≠ 0) :
    rotate (inv q) (rotate q v) = v := by
  rw [rotate_comp, inv_mul q h, rotate_one]

--ai: the opposite inverse composition is also an identity.
theorem rotate_inv_right (q : Qua) (v : F32v3) (h : normSq q ≠ 0) :
    rotate q (rotate (inv q) v) = v := by
  rw [rotate_comp, mul_inv q h, rotate_one]

--ai: unit norm suffices for conjugation to supply the inverse.
theorem inv_eq_conj_unit (q : Qua) (h : normSq q = 1) : inv q = conj q := by
  ext <;> simp [inv, conj, h]

--ai: the unit-quaternion inverse may be implemented by conjugation.
theorem rotate_conj_left_unit (q : Qua) (v : F32v3) (h : normSq q = 1) :
    rotate (conj q) (rotate q v) = v := by
  rw [← inv_eq_conj_unit q h]
  exact rotate_inv_left q v (by rw [h]; norm_num)

--ai: conjugate action also restores the original vector in the other order.
theorem rotate_conj_right_unit (q : Qua) (v : F32v3) (h : normSq q = 1) :
    rotate q (rotate (conj q) v) = v := by
  rw [← inv_eq_conj_unit q h]
  exact rotate_inv_right q v (by rw [h]; norm_num)

--ai: expose why native matrix/vector helpers disagree off the unit sphere.
theorem toMatrix_difference (q : Qua) (v : F32v3) :
    (toMatrix q).transformDir v = F32v3.add (rotate q v) (v.scale (1 - normSq q)) := by
  ext <;> simp [toMatrix, Matrix.transformDir, rotate, F32v3.add, F32v3.scale, normSq] <;> ring

--ai: reuse the actual engine transform convention; no matrix transpose is silently inserted.
theorem toMatrix_transformDir_unit (q : Qua) (v : F32v3) (h : normSq q = 1) :
    (toMatrix q).transformDir v = rotate q v := by
  rw [toMatrix_difference, h]
  ext <;> simp [F32v3.add, F32v3.scale]

--ai: affine point transformation agrees too because the quaternion matrix has zero translation.
theorem toMatrix_transformVec_unit (q : Qua) (v : F32v3) (h : normSq q = 1) :
    (toMatrix q).transformVec v = rotate q v := by
  have hdir := toMatrix_transformDir_unit q v h
  simpa only [toMatrix, Matrix.identity, Matrix.transformVec, Matrix.transformDir, add_zero] using hdir

--ai: native quaternion matrices are also invariant under the antipodal sign change.
theorem toMatrix_neg (q : Qua) : toMatrix (scale q (-1)) = toMatrix q := by
  ext <;> simp [toMatrix, scale]

--ai: identity matrix correspondence is explicit in numeric-field order.
theorem toMatrix_one : toMatrix one = Matrix.identity := by
  ext <;> norm_num [toMatrix, one, Matrix.identity]

--ai: a nonunit scalar quaternion distinguishes the two helper contracts.
theorem nonunit_matrix_counterexample :
    rotate (scale one 2) F32v3.unitX = F32v3.make 4 0 0 ∧
      (toMatrix (scale one 2)).transformDir F32v3.unitX = F32v3.unitX := by
  constructor <;> ext <;>
    norm_num [rotate, scale, one, toMatrix, Matrix.transformDir, F32v3.unitX, F32v3.make]

end Quaternion
end GxMath
