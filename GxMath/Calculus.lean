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
  gxmath/Calculus.lean
  gX — a game engine

  Formal contracts for finite differences and Simpson quadrature in
  src/gxmath/calculus.c.

  The model is over ℝ and uses the exact-zero guard for the step. It does not
  certify the tolerance-based zero test, floating rounding, convergence of
  Newton iteration, or general quadrature convergence. It proves derivative identities
  for constants, the identity, squares, affine functions and linear
  combinations, plus one Newton step on an affine function.
  //ai: the Simpson model mirrors endpoint setup and interior parity weights
  over ℝ, then proves equality with the interval integral of every polynomial
  of degree at most three for a positive, even step count. The callback is
  assumed pure and nonnull; indices are unbounded naturals and float arithmetic is not
  certified. Zero steps return zero; one step is trapezoidal. Odd steps are
  accepted by C but not covered by cubic exactness (an explicit counterexample
  is proved). No native behavior or tolerance is changed.

  Theorems proven:
    - forward-difference constants/identity/square/affine values
    - additivity and homogeneity of the forward difference
    - one Newton step reaches the root of a nonzero-slope affine function
    - //ai: Simpson panel/loop bridge, cubic integration and branch counterexamples
-/

import Mathlib.Data.Real.Basic
--ai: connect algebraic quadrature exactness to the actual signed interval integral.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace GxMath
namespace Calculus

noncomputable def differentiate (f : ℝ → ℝ) (x d : ℝ) : ℝ :=
  if d = 0 then 0 else (f (x + d) - f x) / d

theorem differentiate_zero (x d : ℝ) :
    differentiate (fun _ => 0) x d = 0 := by
  simp [differentiate]

theorem differentiate_const (c x d : ℝ) :
    differentiate (fun _ => c) x d = 0 := by
  simp [differentiate]

theorem differentiate_id (x d : ℝ) (h : d ≠ 0) :
    differentiate (fun y => y) x d = 1 := by
  unfold differentiate
  simp [h]

theorem differentiate_square (x d : ℝ) (h : d ≠ 0) :
    differentiate (fun y => y ^ 2) x d = 2 * x + d := by
  unfold differentiate
  simp [h]
  field_simp [h]
  ring

theorem differentiate_affine (a b x d : ℝ) (h : d ≠ 0) :
    differentiate (fun y => a * y + b) x d = a := by
  unfold differentiate
  simp [h]
  field_simp [h]
  ring

theorem differentiate_add (f g : ℝ → ℝ) (x d : ℝ) :
    differentiate (fun y => f y + g y) x d =
      differentiate f x d + differentiate g x d := by
  by_cases h : d = 0
  · simp [differentiate, h]
  · unfold differentiate
    simp [h]
    field_simp [h]
    ring

theorem differentiate_smul (c : ℝ) (f : ℝ → ℝ) (x d : ℝ) :
    differentiate (fun y => c * f y) x d = c * differentiate f x d := by
  by_cases h : d = 0
  · simp [differentiate, h]
  · unfold differentiate
    simp [h]
    field_simp [h]

noncomputable def newtonStep (f : ℝ → ℝ) (x d : ℝ) : ℝ :=
  x - f x / differentiate f x d

noncomputable def newton (f : ℝ → ℝ) (x0 d : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => newtonStep f (newton f x0 d n) d

theorem newton_affine_one (a b x0 d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) :
    newton (fun y => a * y + b) x0 d 1 = -(b / a) := by
  simp [newton, newtonStep, differentiate_affine, hd]
  field_simp [ha]
  ring

--ai: exact-real accumulation of native interior indices 1 through count.
def simpsonInterior (f : ℝ → ℝ) (a h : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => simpsonInterior f a h k +
      (if (k + 1) % 2 = 0 then 2 else 4) * f (a + (k + 1 : ℕ) * h)

--ai: match native zero/one branches, endpoints, parity weights and h/3 scaling.
noncomputable def simpson (f : ℝ → ℝ) (steps : ℕ) (a b : ℝ) : ℝ :=
  if steps = 0 then 0
  else if steps = 1 then (b - a) * (1 / 2) * (f a + f b)
  else
    let h := (b - a) / (steps : ℝ)
    (f a + f b + simpsonInterior f a h (steps - 1)) * (h / 3)

--ai: paired Simpson panel used only after proving the native-weight bridge.
noncomputable def simpsonPanel (f : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (f a + 4 * f (a + h) + f (a + 2 * h)) * (h / 3)

--ai: adjacent panels telescope on a uniform grid.
noncomputable def simpsonPanels (f : ℝ → ℝ) (a h : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => simpsonPanels f a h k + simpsonPanel f (a + (2 * k : ℕ) * h) h

--ai: arbitrary cubic coefficients also cover degrees zero, one and two.
def cubic (A B C D x : ℝ) : ℝ := A * x ^ 3 + B * x ^ 2 + C * x + D

--ai: signed polynomial antiderivative, later linked to the interval integral.
noncomputable def cubicPrimitive (A B C D x : ℝ) : ℝ :=
  A * x ^ 4 / 4 + B * x ^ 3 / 3 + C * x ^ 2 / 2 + D * x

--ai: the zero-step branch is not an integral-exactness claim.
theorem simpson_zero (f : ℝ → ℝ) (a b : ℝ) : simpson f 0 a b = 0 := by
  simp [simpson]

--ai: the native single-step fallback is explicitly trapezoidal.
theorem simpson_one (f : ℝ → ℝ) (a b : ℝ) :
    simpson f 1 a b = (b - a) * (1 / 2) * (f a + f b) := by
  simp [simpson]

--ai: any finite step count gives zero on a degenerate exact-real interval.
theorem simpson_degenerate (f : ℝ → ℝ) (n : ℕ) (a : ℝ) : simpson f n a a = 0 := by
  simp [simpson]

--ai: one panel integrates every cubic polynomial exactly.
theorem simpson_panel_cubic (A B C D a h : ℝ) :
    simpsonPanel (cubic A B C D) a h =
      cubicPrimitive A B C D (a + 2 * h) - cubicPrimitive A B C D a := by
  unfold simpsonPanel cubic cubicPrimitive
  ring

--ai: the antiderivative differences telescope with no interval-order assumption.
theorem simpson_panels_cubic (A B C D a h : ℝ) (n : ℕ) :
    simpsonPanels (cubic A B C D) a h n =
      cubicPrimitive A B C D (a + (2 * n : ℕ) * h) - cubicPrimitive A B C D a := by
  induction n with
  | zero => simp [simpsonPanels]
  | succ n ih =>
    rw [simpsonPanels, ih, simpson_panel_cubic]
    have hstep : a + (2 * (n + 1) : ℕ) * h = a + (2 * n : ℕ) * h + 2 * h := by
      push_cast
      ring
    rw [hstep]
    ring

--ai: bridge the actual 1,4,2,...,4,1 weights to adjacent panels before claiming exactness.
theorem simpson_even_weights (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    (f a + f (a + (2 * (n + 1) : ℕ) * h) + simpsonInterior f a h (2 * n + 1)) * (h / 3) =
      simpsonPanels f a h (n + 1) := by
  induction n with
  | zero =>
    norm_num only [simpsonInterior, simpsonPanels, simpsonPanel]
    simp only [ite_false]
    ring_nf
  | succ n ih =>
    have hidx : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [hidx, simpsonInterior, simpsonInterior]
    have heven : (2 * n + 1 + 1) % 2 = 0 := by omega
    have hodd : (2 * n + 1 + 1 + 1) % 2 ≠ 0 := by omega
    rw [if_pos heven, if_neg hodd]
    rw [simpsonPanels]
    rw [← ih]
    unfold simpsonPanel
    have hmid : a + ((2 * n + 1 + 1 + 1 : ℕ) : ℝ) * h =
        (a + ((2 * (n + 1) : ℕ) : ℝ) * h) + h := by push_cast; ring
    have hend : a + ((2 * ((n + 1) + 1) : ℕ) : ℝ) * h =
        (a + ((2 * (n + 1) : ℕ) : ℝ) * h) + 2 * h := by push_cast; ring
    have hold : a + ((2 * n + 1 + 1 : ℕ) : ℝ) * h =
        a + ((2 * (n + 1) : ℕ) : ℝ) * h := by congr 2
    rw [hmid, hend, hold]
    ring

--ai: positive even steps connect the native endpoint/loop model to the cubic primitive.
theorem simpson_cubic_exact (A B C D a b : ℝ) (panels : ℕ) (hp : 0 < panels) :
    simpson (cubic A B C D) (2 * panels) a b =
      cubicPrimitive A B C D b - cubicPrimitive A B C D a := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hn0 : 2 * (n + 1) ≠ 0 := by omega
  have hn1 : 2 * (n + 1) ≠ 1 := by omega
  have hden : ((2 * (n + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hend : a + ((2 * (n + 1) : ℕ) : ℝ) * ((b - a) / ((2 * (n + 1) : ℕ) : ℝ)) = b := by
    field_simp
    ring
  have hidx : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [simpson, if_neg hn0, if_neg hn1]
  dsimp only
  have hw := simpson_even_weights (cubic A B C D) a
    ((b - a) / ((2 * (n + 1) : ℕ) : ℝ)) n
  rw [hend] at hw
  rw [hidx, hw, simpson_panels_cubic, hend]

--ai: the one-step trapezoidal branch is exact on affine functions; no general cubic claim.
theorem simpson_one_affine (C D a b : ℝ) :
    simpson (fun x => C * x + D) 1 a b = C * (b ^ 2 - a ^ 2) / 2 + D * (b - a) := by
  rw [simpson_one]
  ring

--ai: odd steps remain accepted by C but do not satisfy general polynomial exactness.
theorem simpson_odd_counterexample : simpson (fun _ => 1) 3 0 1 = (8 / 9 : ℝ) := by
  norm_num [simpson, simpsonInterior]

--ai: the single-step branch is not cubic-exact even for x squared.
theorem simpson_one_quadratic : simpson (fun x => x ^ 2) 1 0 1 = (1 / 2 : ℝ) := by
  norm_num [simpson]

--ai: connect the polynomial primitive to Mathlib's signed interval integral.
theorem cubic_integral (A B C D a b : ℝ) :
    (∫ x in a..b, cubic A B C D x) =
      cubicPrimitive A B C D b - cubicPrimitive A B C D a := by
  have h3 : IntervalIntegrable (fun x : ℝ => A * x ^ 3) MeasureTheory.volume a b :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun x : ℝ => B * x ^ 2) MeasureTheory.volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have h1 : IntervalIntegrable (fun x : ℝ => C * x) MeasureTheory.volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have h0 : IntervalIntegrable (fun _ : ℝ => D) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable a b
  unfold cubic
  rw [intervalIntegral.integral_add ((h3.add h2).add h1) h0,
    intervalIntegral.integral_add (h3.add h2) h1,
    intervalIntegral.integral_add h3 h2]
  rw [intervalIntegral.integral_const_mul C (fun x : ℝ => x), integral_id]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  norm_num
  unfold cubicPrimitive
  ring

--ai: the main exactness theorem covers every real cubic and either interval orientation.
theorem simpson_cubic_integral (A B C D a b : ℝ) (panels : ℕ) (hp : 0 < panels) :
    simpson (cubic A B C D) (2 * panels) a b = ∫ x in a..b, cubic A B C D x := by
  rw [simpson_cubic_exact A B C D a b panels hp, cubic_integral]

--ai: state the native admission condition directly as positive even steps.
theorem simpson_cubic_of_even (A B C D a b : ℝ) (steps : ℕ)
    (hne : steps ≠ 0) (heven : Even steps) :
    simpson (cubic A B C D) steps a b = ∫ x in a..b, cubic A B C D x := by
  obtain ⟨panels, hpanels⟩ := heven
  have heq : steps = 2 * panels := by omega
  have hp : 0 < panels := by omega
  rw [heq]
  exact simpson_cubic_integral A B C D a b panels hp

--ai: explicitly refute applying cubic exactness to the one-step branch.
theorem simpson_one_quadratic_not_exact :
    simpson (fun x => x ^ 2) 1 0 1 ≠ ∫ x : ℝ in (0 : ℝ)..1, x ^ 2 := by
  rw [simpson_one_quadratic]
  norm_num

--ai: explicitly refute applying exactness to an odd step count.
theorem simpson_odd_not_exact :
    simpson (fun _ => 1) 3 0 1 ≠ ∫ _x : ℝ in (0 : ℝ)..1, (1 : ℝ) := by
  rw [simpson_odd_counterexample]
  norm_num

end Calculus
end GxMath
