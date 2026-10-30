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
  gxmath/Physics.lean
  gX — a game engine

  Formal contracts for the SI-exact physics helpers in
  src/gxmath/physics.c (electromagnetism + thermal radiation),
  re-verified against the C source at add time.

  Note: the C library uses IEEE-754 `Float`; as in GxMath/Vector, the formal
  math is modeled over `ℝ`, the exact real semantics the C code approximates.
  Float rounding is bounded separately by the C unit tests and the SymPy
  oracle (scripts/math_pass.py).

  Properties verified:
    - Coulomb force is symmetric in the charge pair and signed by the
      charge product; the pair potential is the force times separation.
    - The electric field is parallel to the offset vector.
    - The Lorentz force is perpendicular to both the velocity (no work) and
      the magnetic field, and flips with the velocity/field swap.
    - Cyclotron radius is positive on the defined domain and antitone in the
      field magnitude.
    - Magnetic dipoles: the axial field is twice the equatorial field; both
      fall off with distance; coaxial moments attract/repel by the sign of
      the moment product; the coaxial force is the aligned potential's
      radial derivative (F = 3·U/r); the torque vector is perpendicular to
      the moment and the field, anti-commutes, vanishes for parallel
      moments, and the textbook magnitude peaks at m·B and never exceeds it.
    - Photon energy, Stefan-Boltzmann power and the Wien peak are positive on
      the defined domain; Stefan-Boltzmann power is monotone in temperature
      and the Wien peak is antitone in temperature.
    - The blackbody sample normalization returns the zero vector for
      non-positive input and bounded [0, 1] channels otherwise.
-/

import GxMath.Vector
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxMath

/-!
## Physical constants

Mirrors `src/gxmath/config.h` (CODATA values, exact rationals here so the
kernel can check positivity).
-/

noncomputable def coulombConstant : ℝ := 89875517923 / 10
noncomputable def magneticConstant : ℝ := 1 / 10 ^ 7
noncomputable def stefanBoltzmannConstant : ℝ := 5670374419 / 10 ^ 17
noncomputable def wienConstant : ℝ := 2897771955 / 10 ^ 12
noncomputable def planckConstant : ℝ := 6626070040 / 10 ^ 43
noncomputable def speedOfLight : ℝ := 299792458

theorem coulombConstant_pos : 0 < coulombConstant := by norm_num [coulombConstant]
theorem magneticConstant_pos : 0 < magneticConstant := by
  norm_num [magneticConstant]
theorem stefanBoltzmannConstant_pos : 0 < stefanBoltzmannConstant := by
  norm_num [stefanBoltzmannConstant]
theorem wienConstant_pos : 0 < wienConstant := by norm_num [wienConstant]
theorem planckConstant_pos : 0 < planckConstant := by norm_num [planckConstant]
theorem speedOfLight_pos : 0 < speedOfLight := by norm_num [speedOfLight]

namespace Physics

open F32v3

/-!
## Electromagnetism

Mirrors gX_F32_Physics_CoulombForce / CoulombPotential /
gX_F32v3_Physics_ElectricField / LorentzForce / CyclotronRadius.
The C NaN guards (d <= 0, r = 0, q = 0/B = 0/speed < 0, wavelength <= 0)
become hypotheses of the defined-domain theorems.
-/

/-- Coulomb force magnitude between two point charges (signed: positive is
repulsion). Mirrors `k · q₁q₂ / d²`. -/
noncomputable def coulombForce (q1 q2 d : ℝ) : ℝ := coulombConstant * q1 * q2 / (d * d)

/-- Coulomb pair potential (signed, zero at infinity). Mirrors `k · q₁q₂ / d`. -/
noncomputable def coulombPotential (q1 q2 d : ℝ) : ℝ := coulombConstant * q1 * q2 / d

/-- Electric field vector at `offset` from a point charge
(`E = k · q · r / |r|³`; zero vector at a zero offset). -/
noncomputable def electricField (q : ℝ) (offset : F32v3) : F32v3 :=
  if offset.lengthSqr ≤ 0 then F32v3.zero
  else offset.scale (coulombConstant * q
    / (offset.lengthSqr * Real.sqrt offset.lengthSqr))

/-- Lorentz force on a charge moving through a magnetic field
(`F = q · (v × B)`). -/
noncomputable def lorentzForce (q : ℝ) (v b : F32v3) : F32v3 := (v.cross b).scale q

/-- Cyclotron radius `r = m·v / (|q|·B)` (zero charge/field and negative
speed are outside the modelled domain). -/
noncomputable def cyclotronRadius (m speed q b : ℝ) : ℝ := m * speed / (|q| * b)

/-- The signed Coulomb magnitude ignores the charge order. -/
theorem coulombForce_comm (q1 q2 d : ℝ) :
    coulombForce q1 q2 d = coulombForce q2 q1 d := by
  simp only [coulombForce]
  ring

/-- Like charges repel (positive signed force). -/
theorem coulombForce_same_sign_pos (q1 q2 d : ℝ) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hd : 0 < d) : 0 < coulombForce q1 q2 d := by
  have hk := coulombConstant_pos
  simp only [coulombForce]
  positivity

/-- Opposite charges attract (negative signed force). -/
theorem coulombForce_opposite_sign_neg (q1 q2 d : ℝ) (hq1 : 0 < q1)
    (hq2 : q2 < 0) (hd : 0 < d) : coulombForce q1 q2 d < 0 := by
  have hk := coulombConstant_pos
  simp only [coulombForce]
  have hnum : coulombConstant * q1 * q2 < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hk hq1) hq2
  have hd2 : 0 < d * d := mul_pos hd hd
  exact div_neg_of_neg_of_pos hnum hd2

/-- The pair potential is the force magnitude times the separation. -/
theorem coulombPotential_eq_force_mul_distance (q1 q2 d : ℝ) (hd : d ≠ 0) :
    coulombPotential q1 q2 d = coulombForce q1 q2 d * d := by
  simp only [coulombPotential, coulombForce]
  field_simp

/-- The pair potential ignores the charge order. -/
theorem coulombPotential_comm (q1 q2 d : ℝ) :
    coulombPotential q1 q2 d = coulombPotential q2 q1 d := by
  simp only [coulombPotential]
  ring

/-- The electric field points along the offset vector (cross product zero). -/
theorem electricField_parallel_offset (q : ℝ) (offset : F32v3) :
    (electricField q offset).cross offset = F32v3.zero := by
  by_cases h : offset.lengthSqr ≤ 0
  · simp [electricField, h, F32v3.cross, F32v3.zero]
  · simp only [electricField, h, if_false]
    ext <;> simp [F32v3.cross, F32v3.scale, F32v3.zero] <;> ring

/-- The magnetic force does no work: it is perpendicular to the velocity. -/
theorem lorentzForce_dot_velocity (q : ℝ) (v b : F32v3) :
    (lorentzForce q v b).dot v = 0 := by
  simp only [lorentzForce, F32v3.scale, F32v3.dot, F32v3.cross]
  ring

/-- The magnetic force is perpendicular to the field. -/
theorem lorentzForce_dot_field (q : ℝ) (v b : F32v3) :
    (lorentzForce q v b).dot b = 0 := by
  simp only [lorentzForce, F32v3.scale, F32v3.dot, F32v3.cross]
  ring

/-- Swapping velocity and field flips the force. -/
theorem lorentzForce_anti_comm (q : ℝ) (v b : F32v3) :
    lorentzForce q v b = -lorentzForce q b v := by
  change lorentzForce q v b = F32v3.neg (lorentzForce q b v)
  ext <;> simp [lorentzForce, F32v3.cross, F32v3.scale, F32v3.neg] <;> ring

/-- The cyclotron radius is positive on the defined domain. -/
theorem cyclotronRadius_pos (m speed q b : ℝ) (hm : 0 < m) (hv : 0 < speed)
    (hq : q ≠ 0) (hb : 0 < b) : 0 < cyclotronRadius m speed q b := by
  simp only [cyclotronRadius]
  have hqabs : 0 < |q| := abs_pos.mpr hq
  exact div_pos (mul_pos hm hv) (mul_pos hqabs hb)

/-- A stronger field tightens the orbit (antitone in the field magnitude). -/
theorem cyclotronRadius_antitone_field (m speed q b1 b2 : ℝ) (hm : 0 < m)
    (hv : 0 < speed) (hq : q ≠ 0) (hb1 : 0 < b1) (hb : b1 ≤ b2) :
    cyclotronRadius m speed q b2 ≤ cyclotronRadius m speed q b1 := by
  simp only [cyclotronRadius]
  have hqabs : 0 < |q| := abs_pos.mpr hq
  have hden1 : 0 < |q| * b1 := mul_pos hqabs hb1
  have hden : |q| * b1 ≤ |q| * b2 := mul_le_mul_of_nonneg_left hb (le_of_lt hqabs)
  have hone : 1 / (|q| * b2) ≤ 1 / (|q| * b1) :=
    one_div_le_one_div_of_le hden1 hden
  have hmv : 0 ≤ m * speed := le_of_lt (mul_pos hm hv)
  calc m * speed / (|q| * b2) = m * speed * (1 / (|q| * b2)) := by ring
    _ ≤ m * speed * (1 / (|q| * b1)) := mul_le_mul_of_nonneg_left hone hmv
    _ = m * speed / (|q| * b1) := by ring

/-!
## Magnetic dipoles

Mirrors gX_F32v3_Physics_DipoleField / DipoleTorque / DipoleForce and the
scalar on-axis/equatorial helpers. The module rotates a magnet's local moment
by its body orientation before these laws apply; the C NaN guards (r = 0,
distance <= 0) become hypotheses of the defined-domain theorems.
-/

/-- On-axis dipole field magnitude `2·(μ0/4π)·m / r³`. -/
noncomputable def dipoleFieldOnAxis (m r : ℝ) : ℝ :=
  2 * magneticConstant * m / (r * r * r)

/-- Equatorial dipole field magnitude `(μ0/4π)·m / r³`. -/
noncomputable def dipoleFieldEquatorial (m r : ℝ) : ℝ :=
  magneticConstant * m / (r * r * r)

/-- Coaxial dipole force (signed along the separation; positive is
repulsion, a positive moment product attracts): `−6·(μ0/4π)·m₁m₂ / r⁴`. -/
noncomputable def dipoleForceOnAxis (m1 m2 r : ℝ) : ℝ :=
  -6 * magneticConstant * m1 * m2 / (r * r * r * r)

/-- Axially aligned pair potential (moments collinear): `−2·(μ0/4π)·m₁m₂/r³`. -/
noncomputable def dipolePotentialAxial (m1 m2 r : ℝ) : ℝ :=
  -2 * magneticConstant * m1 * m2 / (r * r * r)

/-- Torque vector `τ = m × B`. -/
noncomputable def dipoleTorque (m b : F32v3) : F32v3 := m.cross b

/-- Textbook scalar torque magnitude `m·B·sin θ`. -/
noncomputable def dipoleTorqueMagnitude (m b θ : ℝ) : ℝ := m * b * Real.sin θ

/-- The on-axis field is twice the equatorial field at the same distance. -/
theorem dipoleFieldOnAxis_eq_two_equatorial (m r : ℝ) :
    dipoleFieldOnAxis m r = 2 * dipoleFieldEquatorial m r := by
  simp only [dipoleFieldOnAxis, dipoleFieldEquatorial]
  ring

/-- The on-axis field is positive for a positive moment and distance. -/
theorem dipoleFieldOnAxis_pos (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    0 < dipoleFieldOnAxis m r := by
  have hc := magneticConstant_pos
  simp only [dipoleFieldOnAxis]
  positivity

/-- The equatorial field is positive for a positive moment and distance. -/
theorem dipoleFieldEquatorial_pos (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    0 < dipoleFieldEquatorial m r := by
  have hc := magneticConstant_pos
  simp only [dipoleFieldEquatorial]
  positivity

/-- Both fields fall off with distance (antitone in r). -/
theorem dipoleFieldOnAxis_antitone_r (m r1 r2 : ℝ) (hm : 0 < m)
    (hr1 : 0 < r1) (h : r1 ≤ r2) :
    dipoleFieldOnAxis m r2 ≤ dipoleFieldOnAxis m r1 := by
  have hc := magneticConstant_pos
  have h2 : r1 * r1 ≤ r2 * r2 :=
    mul_self_le_mul_self (le_of_lt hr1) h
  have h2' : 0 ≤ r1 * r1 := mul_self_nonneg r1
  have h3 : (r1 * r1) * r1 ≤ (r2 * r2) * r2 :=
    mul_le_mul h2 h (le_of_lt hr1) (le_trans h2' h2)
  have hone : 1 / (r2 * r2 * r2) ≤ 1 / (r1 * r1 * r1) :=
    one_div_le_one_div_of_le (by positivity) h3
  have hfront : 0 ≤ 2 * magneticConstant * m := by positivity
  simp only [dipoleFieldOnAxis]
  calc 2 * magneticConstant * m / (r2 * r2 * r2)
      = 2 * magneticConstant * m * (1 / (r2 * r2 * r2)) := by ring
    _ ≤ 2 * magneticConstant * m * (1 / (r1 * r1 * r1)) :=
        mul_le_mul_of_nonneg_left hone hfront
    _ = 2 * magneticConstant * m / (r1 * r1 * r1) := by ring

/-- Both fields fall off with distance (antitone in r). -/
theorem dipoleFieldEquatorial_antitone_r (m r1 r2 : ℝ) (hm : 0 < m)
    (hr1 : 0 < r1) (h : r1 ≤ r2) :
    dipoleFieldEquatorial m r2 ≤ dipoleFieldEquatorial m r1 := by
  have hc := magneticConstant_pos
  have h2 : r1 * r1 ≤ r2 * r2 :=
    mul_self_le_mul_self (le_of_lt hr1) h
  have h2' : 0 ≤ r1 * r1 := mul_self_nonneg r1
  have h3 : (r1 * r1) * r1 ≤ (r2 * r2) * r2 :=
    mul_le_mul h2 h (le_of_lt hr1) (le_trans h2' h2)
  have hone : 1 / (r2 * r2 * r2) ≤ 1 / (r1 * r1 * r1) :=
    one_div_le_one_div_of_le (by positivity) h3
  have hfront : 0 ≤ magneticConstant * m := by positivity
  simp only [dipoleFieldEquatorial]
  calc magneticConstant * m / (r2 * r2 * r2)
      = magneticConstant * m * (1 / (r2 * r2 * r2)) := by ring
    _ ≤ magneticConstant * m * (1 / (r1 * r1 * r1)) :=
        mul_le_mul_of_nonneg_left hone hfront
    _ = magneticConstant * m / (r1 * r1 * r1) := by ring

/-- Coaxial moments with a positive product attract (negative signed force). -/
theorem dipoleForceOnAxis_neg_of_pos_product (m1 m2 r : ℝ) (hm1 : 0 < m1)
    (hm2 : 0 < m2) (hr : 0 < r) : dipoleForceOnAxis m1 m2 r < 0 := by
  have hc := magneticConstant_pos
  simp only [dipoleForceOnAxis]
  have hpos : 0 < 6 * magneticConstant * m1 * m2 :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hc) hm1) hm2
  have hnum : -6 * magneticConstant * m1 * m2 < 0 := by linarith
  exact div_neg_of_neg_of_pos hnum (mul_pos (mul_pos (mul_pos hr hr) hr) hr)

/-- Coaxial moments with a negative product repel (positive signed force). -/
theorem dipoleForceOnAxis_pos_of_neg_product (m1 m2 r : ℝ) (hm1 : 0 < m1)
    (hm2 : m2 < 0) (hr : 0 < r) : 0 < dipoleForceOnAxis m1 m2 r := by
  have hc := magneticConstant_pos
  simp only [dipoleForceOnAxis]
  have hneg : 0 < -m2 := neg_pos.mpr hm2
  have hpos : 0 < 6 * magneticConstant * m1 * (-m2) :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hc) hm1) hneg
  have hnum : 0 < -6 * magneticConstant * m1 * m2 := by
    have hrew : 6 * magneticConstant * m1 * (-m2)
        = -6 * magneticConstant * m1 * m2 := by ring
    rw [hrew] at hpos
    exact hpos
  exact div_pos hnum (mul_pos (mul_pos (mul_pos hr hr) hr) hr)

/-- The force is the potential's radial derivative in algebraic form
    (`F = 3·U/r` for the axial law, i.e. `F = −dU/dr`). -/
theorem dipoleForceOnAxis_eq_three_potential_div (m1 m2 r : ℝ) (hr : r ≠ 0) :
    dipoleForceOnAxis m1 m2 r = 3 * dipolePotentialAxial m1 m2 r / r := by
  simp only [dipoleForceOnAxis, dipolePotentialAxial]
  field_simp
  ring

/-- The aligned pair potential ignores the moment order. -/
theorem dipolePotentialAxial_comm (m1 m2 r : ℝ) :
    dipolePotentialAxial m1 m2 r = dipolePotentialAxial m2 m1 r := by
  simp only [dipolePotentialAxial]
  ring

/-- The torque is perpendicular to the moment. -/
theorem dipoleTorque_dot_moment (m b : F32v3) :
    (dipoleTorque m b).dot m = 0 := by
  simp only [dipoleTorque, F32v3.cross, F32v3.dot]
  ring

/-- The torque is perpendicular to the field. -/
theorem dipoleTorque_dot_field (m b : F32v3) :
    (dipoleTorque m b).dot b = 0 := by
  simp only [dipoleTorque, F32v3.cross, F32v3.dot]
  ring

/-- Swapping moment and field flips the torque. -/
theorem dipoleTorque_anti_comm (m b : F32v3) :
    dipoleTorque m b = -dipoleTorque b m := by
  change dipoleTorque m b = F32v3.neg (dipoleTorque b m)
  ext <;> simp [dipoleTorque, F32v3.cross, F32v3.neg] <;> ring

/-- A moment parallel to the field feels no torque (equilibrium). -/
theorem dipoleTorque_zero_of_parallel (m : F32v3) (c : ℝ) :
    dipoleTorque m (m.scale c) = F32v3.zero := by
  ext <;> simp [dipoleTorque, F32v3.cross, F32v3.scale, F32v3.zero] <;> ring

/-- Aligned moments feel no torque (the stable equilibrium at θ = 0). -/
theorem dipoleTorqueMagnitude_zero_aligned (m b : ℝ) :
    dipoleTorqueMagnitude m b 0 = 0 := by
  simp [dipoleTorqueMagnitude, Real.sin_zero]

/-- Anti-aligned moments feel no torque (the unstable equilibrium at θ = π). -/
theorem dipoleTorqueMagnitude_zero_antialigned (m b : ℝ) :
    dipoleTorqueMagnitude m b Real.pi = 0 := by
  simp [dipoleTorqueMagnitude, Real.sin_pi]

/-- The torque peaks at θ = π/2 with magnitude `m·B`. -/
theorem dipoleTorqueMagnitude_max (m b : ℝ) :
    dipoleTorqueMagnitude m b (Real.pi / 2) = m * b := by
  simp [dipoleTorqueMagnitude, Real.sin_pi_div_two]

/-- The torque magnitude never exceeds `m·B`. -/
theorem dipoleTorqueMagnitude_le (m b θ : ℝ) (hm : 0 ≤ m) (hb : 0 ≤ b) :
    dipoleTorqueMagnitude m b θ ≤ m * b := by
  have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hmb : 0 ≤ m * b := mul_nonneg hm hb
  simp only [dipoleTorqueMagnitude]
  calc m * b * Real.sin θ ≤ m * b * 1 := mul_le_mul_of_nonneg_left hs hmb
    _ = m * b := by ring

/-- The textbook torque magnitude is nonnegative on the swing [0, π]. -/
theorem dipoleTorqueMagnitude_nonneg (m b θ : ℝ) (hm : 0 ≤ m) (hb : 0 ≤ b)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    0 ≤ dipoleTorqueMagnitude m b θ := by
  have hmem : θ ∈ Set.Icc (0 : ℝ) Real.pi := Set.mem_Icc.mpr ⟨hθ0, hθπ⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hmem
  simp only [dipoleTorqueMagnitude]
  positivity

/-!
## Thermal radiation

Mirrors gX_F32_Physics_PhotonEnergy / Temp_StefanBoltzmann / Temp_WienPeak
and the normalization step of gX_F32v3_Physics_Temp_BlackbodyRGB (the Planck
samples themselves stay oracle-checked by scripts/math_pass.py).
-/

/-- Photon energy `E = h·c / λ`. -/
noncomputable def photonEnergy (wavelength : ℝ) : ℝ := planckConstant * speedOfLight / wavelength

/-- Stefan-Boltzmann radiated power `σ·ε·A·T⁴`. -/
noncomputable def stefanBoltzmann (temperature area emissivity : ℝ) : ℝ :=
  stefanBoltzmannConstant * emissivity * area
    * (temperature * temperature) * (temperature * temperature)

/-- Wien displacement law: peak wavelength `b / T`. -/
noncomputable def wienPeak (temperature : ℝ) : ℝ := wienConstant / temperature

/-- The largest of the three blackbody channels. -/
noncomputable def maxChannel (s : F32v3) : ℝ := max s.x (max s.y s.z)

/-- Normalize a blackbody sample so its largest channel is one; a
non-positive sample returns the zero vector (C: no visible glow). -/
noncomputable def normalizeBlackbodySample (s : F32v3) : F32v3 :=
  if maxChannel s ≤ 0 then F32v3.zero
  else s.scale (1 / maxChannel s)

/-- Photon energy is positive for a positive wavelength. -/
theorem photonEnergy_pos (wavelength : ℝ) (h : 0 < wavelength) :
    0 < photonEnergy wavelength := by
  have hk := planckConstant_pos
  have hc := speedOfLight_pos
  simp only [photonEnergy]
  positivity

/-- Shorter wavelengths carry more energy (antitone in wavelength). -/
theorem photonEnergy_antitone_wavelength (l1 l2 : ℝ) (hl1 : 0 < l1)
    (hl : l1 ≤ l2) : photonEnergy l2 ≤ photonEnergy l1 := by
  have hk := planckConstant_pos
  have hc := speedOfLight_pos
  have hfront : 0 ≤ planckConstant * speedOfLight := le_of_lt (mul_pos hk hc)
  have hone : 1 / l2 ≤ 1 / l1 := one_div_le_one_div_of_le hl1 hl
  simp only [photonEnergy]
  calc planckConstant * speedOfLight / l2
      = planckConstant * speedOfLight * (1 / l2) := by ring_nf
    _ ≤ planckConstant * speedOfLight * (1 / l1) :=
        mul_le_mul_of_nonneg_left hone hfront
    _ = planckConstant * speedOfLight / l1 := by ring_nf

/-- Radiated power is nonnegative across the physical domain. -/
theorem stefanBoltzmann_nonneg (temperature area emissivity : ℝ)
    (ha : 0 ≤ area) (he : 0 ≤ emissivity) (ht : 0 ≤ temperature) :
    0 ≤ stefanBoltzmann temperature area emissivity := by
  have hs := le_of_lt stefanBoltzmannConstant_pos
  simp only [stefanBoltzmann]
  have ht2 : 0 ≤ temperature * temperature := mul_self_nonneg temperature
  positivity

/-- Radiated power grows with temperature (T1 ≤ T2, both nonnegative). -/
theorem stefanBoltzmann_mono_temperature (t1 t2 area emissivity : ℝ)
    (ha : 0 ≤ area) (he : 0 ≤ emissivity) (ht1 : 0 ≤ t1) (ht : t1 ≤ t2) :
    stefanBoltzmann t1 area emissivity ≤ stefanBoltzmann t2 area emissivity := by
  have hs := le_of_lt stefanBoltzmannConstant_pos
  have h2 : t1 * t1 ≤ t2 * t2 := mul_self_le_mul_self ht1 ht
  have h2' : 0 ≤ t1 * t1 := mul_self_nonneg t1
  have h4 : (t1 * t1) * (t1 * t1) ≤ (t2 * t2) * (t2 * t2) :=
    mul_le_mul h2 h2 h2' (le_trans h2' h2)
  simp only [stefanBoltzmann]
  have hfront : 0 ≤ stefanBoltzmannConstant * emissivity * area := by positivity
  calc stefanBoltzmannConstant * emissivity * area * (t1 * t1) * (t1 * t1)
      = stefanBoltzmannConstant * emissivity * area * ((t1 * t1) * (t1 * t1)) := by ring
    _ ≤ stefanBoltzmannConstant * emissivity * area * ((t2 * t2) * (t2 * t2)) :=
        mul_le_mul_of_nonneg_left h4 hfront
    _ = stefanBoltzmannConstant * emissivity * area * (t2 * t2) * (t2 * t2) := by ring

/-- The Wien peak is positive for positive temperature. -/
theorem wienPeak_pos (temperature : ℝ) (h : 0 < temperature) :
    0 < wienPeak temperature := by
  have hb := wienConstant_pos
  simp only [wienPeak]
  positivity

/-- Hotter bodies peak at shorter wavelengths (antitone in temperature). -/
theorem wienPeak_antitone (t1 t2 : ℝ) (ht1 : 0 < t1) (ht : t1 ≤ t2) :
    wienPeak t2 ≤ wienPeak t1 := by
  have hb := wienConstant_pos
  have hone : 1 / t2 ≤ 1 / t1 := one_div_le_one_div_of_le ht1 ht
  have hb' : 0 ≤ wienConstant := le_of_lt hb
  simp only [wienPeak]
  calc wienConstant / t2 = wienConstant * (1 / t2) := by ring_nf
    _ ≤ wienConstant * (1 / t1) := mul_le_mul_of_nonneg_left hone hb'
    _ = wienConstant / t1 := by ring_nf

/-- A non-positive sample normalizes to the zero vector (no glow). -/
theorem normalizeBlackbodySample_zero_of_nonpos (s : F32v3)
    (h : maxChannel s ≤ 0) : normalizeBlackbodySample s = F32v3.zero := by
  simp [normalizeBlackbodySample, h]

/-- Physically sampled channels (nonnegative, the Planck case) normalize into
[0, 1]. -/
theorem normalizeBlackbodySample_channels_bounded (s : F32v3)
    (hs : 0 ≤ s.x) (hsy : 0 ≤ s.y) (hsz : 0 ≤ s.z)
    (h : 0 < maxChannel s) :
    0 ≤ (normalizeBlackbodySample s).x ∧ (normalizeBlackbodySample s).x ≤ 1 ∧
    0 ≤ (normalizeBlackbodySample s).y ∧ (normalizeBlackbodySample s).y ≤ 1 ∧
    0 ≤ (normalizeBlackbodySample s).z ∧ (normalizeBlackbodySample s).z ≤ 1 := by
  have hx : s.x ≤ maxChannel s := le_max_left _ _
  have hy : s.y ≤ maxChannel s := le_trans (le_max_left _ _) (le_max_right _ _)
  have hz : s.z ≤ maxChannel s := le_trans (le_max_right _ _) (le_max_right _ _)
  simp only [normalizeBlackbodySample, if_neg (not_le.mpr h), F32v3.scale,
    mul_one_div]
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_⟩
  · exact (div_le_one h).mpr hx
  · exact (div_le_one h).mpr hy
  · exact (div_le_one h).mpr hz

end Physics

end GxMath
