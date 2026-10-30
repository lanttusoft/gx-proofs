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
  gxmath/Fourier.lean
  gX — a game engine

  Formal contracts for the discrete Fourier transform modeled by
  src/gxmath/fourier.c.

  This pins the exact-complex DFT convention used by the numeric FFT oracle:
  X[k] = Σ_j x[j] e^(-2πikj/n), with no forward normalization.
  //ai: the inverse uses the positive exponential and 1/n. Explicit Fin/ZMod
  bridges transfer Mathlib inversion to the original exponential definition;
  adjoint identities then yield Parseval. Inversion/Parseval require n ≠ 0.
  This does not model the iterative radix-2 workspace, floating rounding or
  sine-bin phase. There is no native inverse FFT in gX: idft is a specification.

  Theorems proven:
    - DFT linearity in the input sequence
    - zero-sequence response
    - DFT of a delta equals the corresponding exponential kernel
    - DC response of a delta at index zero
    - //ai: index/character bridges, both inverse round trips and Parseval
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
--ai: finite Fourier inversion is bridged to the explicit Fin-indexed exponential model below.
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

open scoped BigOperators

namespace GxMath
namespace Fourier

noncomputable def dft (n : ℕ) (x : Fin n → ℂ) (k : Fin n) : ℂ :=
  ∑ j : Fin n,
    x j * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (n : ℂ)))

def delta (n : ℕ) (j0 : Fin n) : Fin n → ℂ :=
  fun j => if j = j0 then 1 else 0

theorem dft_zero (n : ℕ) (k : Fin n) :
    dft n (fun _ => 0) k = 0 := by
  simp [dft]

theorem dft_add (n : ℕ) (x y : Fin n → ℂ) (k : Fin n) :
    dft n (fun j => x j + y j) k = dft n x k + dft n y k := by
  simp [dft, add_mul, Finset.sum_add_distrib]

theorem dft_smul (n : ℕ) (c : ℂ) (x : Fin n → ℂ) (k : Fin n) :
    dft n (fun j => c * x j) k = c * dft n x k := by
  simp [dft, Finset.mul_sum, mul_assoc]

theorem dft_delta (n : ℕ) (j0 k : Fin n) :
    dft n (delta n j0) k =
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (j0 : ℂ) / (n : ℂ))) := by
  classical
  simp [dft, delta]

theorem dft_delta_zero (n : ℕ) [NeZero n] (k : Fin n) :
    dft n (delta n 0) k = 1 := by
  rw [dft_delta]
  simp

--ai: positive exponential with 1/n scaling; no native inverse FFT is asserted.
noncomputable def idft (n : ℕ) (x : Fin n → ℂ) (k : Fin n) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j : Fin n,
    x j * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (n : ℂ))

--ai: preserve sample ordering when changing from Fin n to ZMod n.
noncomputable def zSignal (n : ℕ) [NeZero n] (x : Fin n → ℂ) (j : ZMod n) : ℂ :=
  x ((ZMod.finEquiv n).symm j)

--ai: the finite ring equivalence sends each index to its natural residue.
theorem finEquiv_eq_natCast (n : ℕ) [NeZero n] (j : Fin n) :
    ZMod.finEquiv n j = (j.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (Fin.cast_val_eq_self j).symm

--ai: positive character formula, including both index factors and transform length.
theorem character_positive (n : ℕ) [NeZero n] (j k : Fin n) :
    ZMod.stdAddChar (ZMod.finEquiv n j * ZMod.finEquiv n k) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (n : ℂ)) := by
  rw [finEquiv_eq_natCast, finEquiv_eq_natCast]
  have hcast : (j.val : ZMod n) * (k.val : ZMod n) =
      (Int.cast ((j.val : ℤ) * (k.val : ℤ)) : ZMod n) := by push_cast; rfl
  rw [hcast, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

--ai: the existing forward transform has the negative character convention.
theorem character_negative (n : ℕ) [NeZero n] (j k : Fin n) :
    ZMod.stdAddChar (-(ZMod.finEquiv n j * ZMod.finEquiv n k)) =
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (n : ℂ))) := by
  rw [finEquiv_eq_natCast, finEquiv_eq_natCast]
  have hcast : -((j.val : ZMod n) * (k.val : ZMod n)) =
      (Int.cast (-((j.val : ℤ) * (k.val : ℤ))) : ZMod n) := by push_cast; rfl
  rw [hcast, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

--ai: this bridge proves agreement with the existing exponential definition, not a new DFT.
theorem dft_zmod_bridge (n : ℕ) [NeZero n] (x : Fin n → ℂ) (k : Fin n) :
    ZMod.dft (zSignal n x) (ZMod.finEquiv n k) = dft n x k := by
  rw [ZMod.dft_apply]
  rw [← (ZMod.finEquiv n).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  change ZMod.stdAddChar (-(ZMod.finEquiv n j * ZMod.finEquiv n k)) *
    x ((ZMod.finEquiv n).symm (ZMod.finEquiv n j)) = _
  rw [RingEquiv.symm_apply_apply, character_negative]
  ring

--ai: the inverse bridge fixes both the sign and the 1/n normalization.
theorem idft_zmod_bridge (n : ℕ) [NeZero n] (x : Fin n → ℂ) (k : Fin n) :
    ZMod.dft.symm (zSignal n x) (ZMod.finEquiv n k) = idft n x k := by
  rw [ZMod.invDFT_apply]
  rw [← (ZMod.finEquiv n).toEquiv.sum_comp]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change ZMod.stdAddChar (ZMod.finEquiv n j * ZMod.finEquiv n k) *
    x ((ZMod.finEquiv n).symm (ZMod.finEquiv n j)) = _
  rw [RingEquiv.symm_apply_apply, character_positive]
  ring

--ai: lift a forward-transformed sample sequence without changing its indices.
theorem zSignal_dft (n : ℕ) [NeZero n] (x : Fin n → ℂ) :
    zSignal n (dft n x) = ZMod.dft (zSignal n x) := by
  funext j
  obtain ⟨k, rfl⟩ := (ZMod.finEquiv n).surjective j
  change dft n x ((ZMod.finEquiv n).symm (ZMod.finEquiv n k)) = _
  rw [RingEquiv.symm_apply_apply]
  exact (dft_zmod_bridge n x k).symm

--ai: lift the explicit positive-sign inverse sequence in the same sample order.
theorem zSignal_idft (n : ℕ) [NeZero n] (x : Fin n → ℂ) :
    zSignal n (idft n x) = ZMod.dft.symm (zSignal n x) := by
  funext j
  obtain ⟨k, rfl⟩ := (ZMod.finEquiv n).surjective j
  change idft n x ((ZMod.finEquiv n).symm (ZMod.finEquiv n k)) = _
  rw [RingEquiv.symm_apply_apply]
  exact (idft_zmod_bridge n x k).symm

--ai: exact inverse-after-forward identity for every nonzero transform length.
theorem idft_dft (n : ℕ) [NeZero n] (x : Fin n → ℂ) (k : Fin n) :
    idft n (dft n x) k = x k := by
  have h := idft_zmod_bridge n (dft n x) k
  rw [zSignal_dft] at h
  simpa only [LinearEquiv.symm_apply_apply, zSignal, RingEquiv.symm_apply_apply] using h.symm

--ai: exact forward-after-inverse identity with the same normalization.
theorem dft_idft (n : ℕ) [NeZero n] (x : Fin n → ℂ) (k : Fin n) :
    dft n (idft n x) k = x k := by
  have h := dft_zmod_bridge n (idft n x) k
  rw [zSignal_idft] at h
  simpa only [LinearEquiv.apply_symm_apply, zSignal, RingEquiv.symm_apply_apply] using h.symm

--ai: conjugation flips the forward sign; swapping factors preserves the kernel.
theorem kernel_conj (n : ℕ) (k j : Fin n) :
    starRingEnd ℂ (Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (n : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (k : ℂ) / (n : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_div₀, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_natCast]
  ring

--ai: finite-sum adjoint identity, before inverse normalization is applied.
theorem dft_adjoint (n : ℕ) (x y : Fin n → ℂ) :
    (∑ k : Fin n, starRingEnd ℂ (dft n x k) * y k) =
      ∑ j : Fin n, starRingEnd ℂ (x j) *
        (∑ k : Fin n, y k * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (k : ℂ) / (n : ℂ))) := by
  unfold dft
  simp_rw [map_sum, map_mul, kernel_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

--ai: the unnormalized forward adjoint is n times the normalized inverse.
theorem dft_pairing (n : ℕ) [NeZero n] (x y : Fin n → ℂ) :
    (∑ k : Fin n, starRingEnd ℂ (dft n x k) * y k) =
      (n : ℂ) * ∑ j : Fin n, starRingEnd ℂ (x j) * idft n y j := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h (j : Fin n) :
      (∑ k : Fin n, y k * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (k : ℂ) / (n : ℂ))) =
        (n : ℂ) * idft n y j := by
    unfold idft
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [dft_adjoint]
  simp_rw [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

--ai: Parseval for the unnormalized forward DFT; normSq includes both complex channels.
theorem parseval (n : ℕ) [NeZero n] (x : Fin n → ℂ) :
    (∑ k : Fin n, Complex.normSq (dft n x k)) =
      (n : ℝ) * ∑ j : Fin n, Complex.normSq (x j) := by
  have h := dft_pairing n x (dft n x)
  simp_rw [idft_dft, ← Complex.normSq_eq_conj_mul_self] at h
  have hre := congrArg Complex.re h
  simpa using hre

--ai: normalized spectral energy equals input energy, with explicit nonzero n.
theorem parseval_normalized (n : ℕ) [NeZero n] (x : Fin n → ℂ) :
    (∑ k : Fin n, Complex.normSq (dft n x k)) / (n : ℝ) =
      ∑ j : Fin n, Complex.normSq (x j) := by
  rw [parseval]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

end Fourier
end GxMath
