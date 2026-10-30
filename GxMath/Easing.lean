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
  gX — Easing Function Invariants

  Formalizes the easing functions from `src/gxmath/easing.c`
  (formulas re-verified against gX easing.c at salvage time:
  Linear/Quad/BezierS/Bezier match exactly; SmoothStep/QuadIn/Out
  are the unit-interval normal forms).

  Key facts:
    - EasingLinear(s, e, t) = (1-t)·s + t·e interpolates endpoints exactly
    - EasingQuad(s, e, t) = (1-t)²·s + t²·e hits endpoints exactly
    - EasingBezierS(s, e, t) = EasingBezier(s, s, e, e, t) (single-control cubic)
    - EasingBezier(s, sc, ec, e, t) is the cubic Bezier with Bernstein basis:
        b0=(1-t)³, b1=3(1-t)²t, b2=3(1-t)t², b3=t³
    - For t ∈ [0,1] the Bernstein weights are all ≥ 0 and sum to 1, so
      EasingBezier is a convex combination → the output stays within the
      bounds of the four control points (in particular [start, ed] when
      start ≤ ed and the controls lie inside).
    - EaseSmoothStep(t) = t²(3-2t) satisfies 0 → 0 and 1 → 1 and stays
      inside [0,1] for t ∈ [0,1].
    - EaseQuadIn(t) = t² and EaseQuadOut(t) = t(2-t) both map [0,1] → [0,1]
      and hit 0 at t=0, 1 at t=1.

  Theorems proven: 21
    - easingLinear_at_0:      EasingLinear(start, ed, 0) = start
    - easingLinear_at_1:      EasingLinear(start, ed, 1) = ed
    - easingLinear_between:   EasingLinear stays within [start, ed]
    - easingQuad_at_0:        EasingQuad(start, ed, 0) = start
    - easingQuad_at_1:        EasingQuad(start, ed, 1) = ed
    - easingBezierS_at_0:     EasingBezierS(start, ed, 0) = start
    - easingBezierS_at_1:     EasingBezierS(start, ed, 1) = ed
    - easingBezier_at_0:      EasingBezier(start, sc, ec, ed, 0) = start
    - easingBezier_at_1:      EasingBezier(start, sc, ec, ed, 1) = ed
    - bernstein_nonneg:       all 4 Bernstein weights ≥ 0 for t ∈ [0,1]
    - bernstein_sum:          b0 + b1 + b2 + b3 = 1
    - bezier_within_bounds:   EasingBezier output within control bounds
    - smoothstep_at_0:        EaseSmoothStep(0) = 0
    - smoothstep_at_1:        EaseSmoothStep(1) = 1
    - smoothstep_between:     EaseSmoothStep stays within [0,1]
    - quadIn_at_0/1:          EaseQuadIn endpoints
    - quadIn_between:         EaseQuadIn stays within [0,1]
    - quadOut_at_0/1:         EaseQuadOut endpoints
    - quadOut_between:        EaseQuadOut stays within [0,1]

  Continuous math is modeled over ℝ (exact real semantics of the Float
  arithmetic). Discrete gX_Easing dispatch (the enum switch) is not modeled
  here — each easing curve is a pure function.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxMath.Easing

-- =============================================================
-- 1. Linear easing
-- =============================================================

-- gX_F32_EasingLinear(start, ed, t) = (1 - t)*start + t*ed
noncomputable def EasingLinear (start ed t : ℝ) : ℝ :=
  (1 - t) * start + t * ed

theorem easingLinear_at_0 (start ed : ℝ) : EasingLinear start ed 0 = start := by
  unfold EasingLinear
  ring

theorem easingLinear_at_1 (start ed : ℝ) : EasingLinear start ed 1 = ed := by
  unfold EasingLinear
  ring

-- For t ∈ [0,1] and start ≤ ed, the linear interpolation stays in between.
theorem easingLinear_between (start ed t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (h : start ≤ ed) :
    start ≤ EasingLinear start ed t ∧ EasingLinear start ed t ≤ ed := by
  unfold EasingLinear
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hdiff : 0 ≤ ed - start := by linarith
  constructor
  · have hte : 0 ≤ t * (ed - start) := mul_nonneg ht0 hdiff
    nlinarith
  · have hte : t * (ed - start) ≤ ed - start := by
      have htmp : (ed - start) * t ≤ ed - start := mul_le_of_le_one_right hdiff ht1
      rwa [mul_comm] at htmp
    nlinarith

-- =============================================================
-- 2. Quadratic easing
-- =============================================================

-- gX_F32_EasingQuad(start, ed, t) = (1-t)²·start + t²·ed
noncomputable def EasingQuad (start ed t : ℝ) : ℝ :=
  (1 - t) * (1 - t) * start + t * t * ed

theorem easingQuad_at_0 (start ed : ℝ) : EasingQuad start ed 0 = start := by
  unfold EasingQuad
  ring

theorem easingQuad_at_1 (start ed : ℝ) : EasingQuad start ed 1 = ed := by
  unfold EasingQuad
  ring

-- =============================================================
-- 3. Cubic Bezier easing
-- =============================================================

-- Bernstein basis weights for the cubic Bezier (b0..b3).
noncomputable def b0 (t : ℝ) : ℝ := (1 - t) ^ 3
noncomputable def b1 (t : ℝ) : ℝ := 3 * (1 - t) ^ 2 * t
noncomputable def b2 (t : ℝ) : ℝ := 3 * (1 - t) * t ^ 2
noncomputable def b3 (t : ℝ) : ℝ := t ^ 3

-- gX_F32_EasingBezierS(start, ed, t): the cubic Bezier with control points
-- start, start, ed, ed — i.e. EasingBezier(start, start, ed, ed, t).
noncomputable def EasingBezierS (start ed t : ℝ) : ℝ :=
  b0 t * start + b1 t * start + b2 t * ed + b3 t * ed

-- gX_F32_EasingBezier(start, startc, endc, ed, t): the cubic Bezier with
-- the four control points (start, startc, endc, ed).
noncomputable def EasingBezier (start startc endc ed t : ℝ) : ℝ :=
  b0 t * start + b1 t * startc + b2 t * endc + b3 t * ed

theorem easingBezierS_at_0 (start ed : ℝ) : EasingBezierS start ed 0 = start := by
  unfold EasingBezierS b0 b1 b2 b3
  ring

theorem easingBezierS_at_1 (start ed : ℝ) : EasingBezierS start ed 1 = ed := by
  unfold EasingBezierS b0 b1 b2 b3
  ring

theorem easingBezier_at_0 (start startc endc ed : ℝ) : EasingBezier start startc endc ed 0 = start := by
  unfold EasingBezier b0 b1 b2 b3
  ring

theorem easingBezier_at_1 (start startc endc ed : ℝ) : EasingBezier start startc endc ed 1 = ed := by
  unfold EasingBezier b0 b1 b2 b3
  ring

-- All four Bernstein weights are non-negative for t ∈ [0,1].
theorem bernstein_nonneg (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ b0 t ∧ 0 ≤ b1 t ∧ 0 ≤ b2 t ∧ 0 ≤ b3 t := by
  unfold b0 b1 b2 b3
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1t0 : 0 ≤ 1 - t := by linarith
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  · positivity

-- The Bernstein basis sums to 1 for any t.
theorem bernstein_sum (t : ℝ) : b0 t + b1 t + b2 t + b3 t = 1 := by
  unfold b0 b1 b2 b3
  ring

-- Since the weights are a convex combination, the Bezier output lies within
-- the min..max of the control points. We state the version that matters for
-- easing: when start ≤ ed and both controls are between them, output is in
-- [start, ed].
theorem bezier_within_bounds (start startc endc ed t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (h1 : start ≤ startc) (h2 : startc ≤ endc) (h3 : endc ≤ ed) :
    start ≤ EasingBezier start startc endc ed t ∧ EasingBezier start startc endc ed t ≤ ed := by
  unfold EasingBezier
  have hw0 : 0 ≤ b0 t := (bernstein_nonneg t ht).1
  have hw1 : 0 ≤ b1 t := (bernstein_nonneg t ht).2.1
  have hw2 : 0 ≤ b2 t := (bernstein_nonneg t ht).2.2.1
  have hw3 : 0 ≤ b3 t := (bernstein_nonneg t ht).2.2.2
  have hs : b0 t + b1 t + b2 t + b3 t = 1 := bernstein_sum t
  have hle01 : start ≤ startc := h1
  have hle02 : start ≤ endc := by linarith
  have hle03 : start ≤ ed := by linarith
  have hle13 : startc ≤ ed := by linarith
  have hle23 : endc ≤ ed := h3
  constructor
  · have h0 : b0 t * start ≤ b0 t * start := le_rfl
    have h1' : b1 t * start ≤ b1 t * startc := mul_le_mul_of_nonneg_left hle01 hw1
    have h2' : b2 t * start ≤ b2 t * endc := mul_le_mul_of_nonneg_left hle02 hw2
    have h3' : b3 t * start ≤ b3 t * ed := mul_le_mul_of_nonneg_left hle03 hw3
    have hgoal1 : start * (b0 t + b1 t + b2 t + b3 t) ≤
        b0 t * start + b1 t * startc + b2 t * endc + b3 t * ed := by
      nlinarith
    rw [hs] at hgoal1
    ring_nf at hgoal1
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgoal1
  · have h0 : b0 t * startc ≤ b0 t * ed := mul_le_mul_of_nonneg_left hle13 hw0
    have h1' : b1 t * startc ≤ b1 t * ed := mul_le_mul_of_nonneg_left hle13 hw1
    have h2' : b2 t * endc ≤ b2 t * ed := mul_le_mul_of_nonneg_left hle23 hw2
    have h3' : b3 t * ed ≤ b3 t * ed := le_rfl
    have hgoal2 : b0 t * start + b1 t * startc + b2 t * endc + b3 t * ed ≤
        ed * (b0 t + b1 t + b2 t + b3 t) := by
      nlinarith
    rw [hs] at hgoal2
    ring_nf at hgoal2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgoal2

-- =============================================================
-- 4. SmoothStep
-- =============================================================

-- gX_F32_EaseSmoothStep(t) = t²(3-2t)
noncomputable def EaseSmoothStep (t : ℝ) : ℝ :=
  t * t * (3 - 2 * t)

theorem smoothstep_at_0 : EaseSmoothStep 0 = 0 := by
  unfold EaseSmoothStep
  ring

theorem smoothstep_at_1 : EaseSmoothStep 1 = 1 := by
  unfold EaseSmoothStep
  ring

-- For t ∈ [0,1], smoothstep stays in [0,1].
theorem smoothstep_between (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ EaseSmoothStep t ∧ EaseSmoothStep t ≤ 1 := by
  unfold EaseSmoothStep
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  constructor
  · have h30 : 0 ≤ 3 - 2 * t := by nlinarith
    have hmm : 0 ≤ (t * t) * (3 - 2 * t) := mul_nonneg (mul_self_nonneg t) h30
    simpa [mul_assoc] using hmm
  · -- 1 - t²(3-2t) = (1-t)²(1+2t) ≥ 0
    have hsq : (1 - t) ^ 2 * (1 + 2 * t) = 1 - t * t * (3 - 2 * t) := by ring
    have h12 : 0 ≤ 1 + 2 * t := by nlinarith
    have hpos : 0 ≤ (1 - t) ^ 2 * (1 + 2 * t) := mul_nonneg (sq_nonneg (1 - t)) h12
    have hle : 0 ≤ 1 - t * t * (3 - 2 * t) := by
      rwa [← hsq]
    nlinarith

-- =============================================================
-- 5. Quad in / out (Robert Penner t-remap helpers)
-- =============================================================

-- gX_F32_EaseQuadIn(t) = t²
noncomputable def EaseQuadIn (t : ℝ) : ℝ := t * t

-- gX_F32_EaseQuadOut(t) = t(2-t)
noncomputable def EaseQuadOut (t : ℝ) : ℝ := t * (2 - t)

theorem quadIn_at_0 : EaseQuadIn 0 = 0 := by unfold EaseQuadIn; ring

theorem quadIn_at_1 : EaseQuadIn 1 = 1 := by unfold EaseQuadIn; ring

theorem quadIn_between (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : 0 ≤ EaseQuadIn t ∧ EaseQuadIn t ≤ 1 := by
  unfold EaseQuadIn
  constructor <;> nlinarith

theorem quadOut_at_0 : EaseQuadOut 0 = 0 := by unfold EaseQuadOut; ring

theorem quadOut_at_1 : EaseQuadOut 1 = 1 := by unfold EaseQuadOut; ring

theorem quadOut_between (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : 0 ≤ EaseQuadOut t ∧ EaseQuadOut t ≤ 1 := by
  unfold EaseQuadOut
  constructor <;> nlinarith

end GxMath.Easing
