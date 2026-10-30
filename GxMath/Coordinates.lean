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
  gX — coordinate contracts for src/gxmath/convert.c.
  //ai: exact-real cylindrical/spherical formulas, angles in radians.

  Cylindrical fields are (radius, azimuth, height); spherical fields are
  (radius, azimuth, polar inclination from +z). atan2(y,x) is modeled by
  Complex.arg (x + iy), using (-pi,pi] and arg(0)=0. Signed-zero branches,
  IEEE atan2/sqrt/acos, underflow and overflow are not certified. Real division
  is totalized at zero; spherical C correspondence excludes the origin.
  Full angular round trips exclude zero cylindrical radius and spherical
  poles, where azimuth is unidentifiable. No native behavior is changed.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import GxMath.Vector

namespace GxMath.Coordinates

--ai: the complex plane is only a bridge for the atan2 convention.
def xy (p : F32v3) : ℂ := ⟨p.x, p.y⟩

--ai: match the native planar sqrt formula exactly over the reals.
noncomputable def planarRadius (p : F32v3) : ℝ := Real.sqrt (p.x * p.x + p.y * p.y)

--ai: model atan2(y,x) with an explicit principal-argument convention.
noncomputable def cartesianToCylinder (p : F32v3) : F32v3 :=
  { x := planarRadius p, y := Complex.arg (xy p), z := p.z }

--ai: only positive spherical radius is used for the Cartesian round-trip theorem.
noncomputable def cartesianToSpherical (p : F32v3) : F32v3 :=
  { x := p.length, y := Complex.arg (xy p), z := Real.arccos (p.z / p.length) }

--ai: native cylindrical reconstruction, without angle wrapping.
noncomputable def cylinderToCartesian (c : F32v3) : F32v3 :=
  { x := c.x * Real.cos c.y, y := c.x * Real.sin c.y, z := c.z }

--ai: direct cylindrical-to-spherical helper preserves the supplied azimuth.
noncomputable def cylinderToSpherical (c : F32v3) : F32v3 :=
  let radius := Real.sqrt (c.x * c.x + c.z * c.z)
  { x := radius, y := c.y, z := Real.arccos (c.z / radius) }

--ai: native spherical reconstruction uses inclination, not altitude.
noncomputable def sphericalToCartesian (s : F32v3) : F32v3 :=
  { x := s.x * Real.sin s.z * Real.cos s.y
    y := s.x * Real.sin s.z * Real.sin s.y
    z := s.x * Real.cos s.z }

--ai: the cylindrical radius is nonnegative for canonical spherical inputs.
noncomputable def sphericalToCylinder (s : F32v3) : F32v3 :=
  { x := s.x * Real.sin s.z, y := s.y, z := s.x * Real.cos s.z }

--ai: bridge planar sqrt to the standard complex norm, including the origin.
theorem xy_norm (p : F32v3) : ‖xy p‖ = planarRadius p := by
  rfl

--ai: the modeled atan2 always returns the declared principal branch.
theorem azimuth_range (p : F32v3) : Complex.arg (xy p) ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

--ai: cylindrical Cartesian reconstruction is geometric even when planar radius is zero.
theorem cartesian_cylinder_cartesian (p : F32v3) :
    cylinderToCartesian (cartesianToCylinder p) = p := by
  have hx := Complex.norm_mul_cos_arg (xy p)
  have hy := Complex.norm_mul_sin_arg (xy p)
  rw [xy_norm] at hx hy
  ext
  · exact hx
  · exact hy
  · rfl

--ai: polar form of reconstructed cylindrical x/y, for branch-sensitive inverse proofs.
theorem xy_cylinder (c : F32v3) :
    xy (cylinderToCartesian c) = (c.x : ℂ) * (Real.cos c.y + Real.sin c.y * Complex.I) := by
  apply Complex.ext <;> simp [xy, cylinderToCartesian, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

--ai: reconstruction recovers the absolute radius, not a signed radial coordinate.
theorem cylinder_planarRadius (c : F32v3) :
    planarRadius (cylinderToCartesian c) = |c.x| := by
  unfold planarRadius cylinderToCartesian
  have h : c.x * Real.cos c.y * (c.x * Real.cos c.y) +
      c.x * Real.sin c.y * (c.x * Real.sin c.y) = c.x ^ 2 := by
    ring_nf
    simp only [Real.cos_sq']
    ring
  rw [h, Real.sqrt_sq_eq_abs]

--ai: arbitrary azimuths round-trip after wrapping, for strictly positive cylindrical radius.
theorem cylinder_azimuth_wrapped (c : F32v3) (hr : 0 < c.x) :
    (cartesianToCylinder (cylinderToCartesian c)).y =
      toIocMod Real.two_pi_pos (-Real.pi) c.y := by
  change Complex.arg (xy (cylinderToCartesian c)) = _
  rw [xy_cylinder]
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr c.y

--ai: full cylindrical tuple equality needs a positive radius and the principal azimuth branch.
theorem cylinder_cartesian_cylinder (c : F32v3) (hr : 0 < c.x)
    (ha : c.y ∈ Set.Ioc (-Real.pi) Real.pi) :
    cartesianToCylinder (cylinderToCartesian c) = c := by
  ext
  · exact (cylinder_planarRadius c).trans (abs_of_pos hr)
  · change Complex.arg (xy (cylinderToCartesian c)) = c.y
    rw [xy_cylinder]
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I hr ha
  · rfl

--ai: sphere-to-cylinder followed by cylindrical reconstruction matches the direct native formula.
theorem spherical_cylinder_cartesian (s : F32v3) :
    cylinderToCartesian (sphericalToCylinder s) = sphericalToCartesian s := by
  rfl

--ai: spherical reconstruction has absolute radius for arbitrary supplied angles.
theorem spherical_length (s : F32v3) : (sphericalToCartesian s).length = |s.x| := by
  unfold F32v3.length sphericalToCartesian F32v3.lengthSqr
  have h : (s.x * Real.sin s.z * Real.cos s.y) * (s.x * Real.sin s.z * Real.cos s.y) +
      (s.x * Real.sin s.z * Real.sin s.y) * (s.x * Real.sin s.z * Real.sin s.y) +
      (s.x * Real.cos s.z) * (s.x * Real.cos s.z) = s.x ^ 2 := by
    ring_nf
    simp only [Real.cos_sq']
    ring
  rw [h, Real.sqrt_sq_eq_abs]

--ai: canonical spherical tuples recover azimuth only away from both polar axes.
theorem spherical_cartesian_spherical (s : F32v3) (hr : 0 < s.x)
    (ha : s.y ∈ Set.Ioc (-Real.pi) Real.pi) (ht : s.z ∈ Set.Ioo 0 Real.pi) :
    cartesianToSpherical (sphericalToCartesian s) = s := by
  have hp : 0 < s.x * Real.sin s.z := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  ext
  · exact (spherical_length s).trans (abs_of_pos hr)
  · change Complex.arg (xy (sphericalToCartesian s)) = s.y
    rw [← spherical_cylinder_cartesian, xy_cylinder]
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, sphericalToCylinder] using
      Complex.arg_mul_cos_add_sin_mul_I hp ha
  · change Real.arccos ((s.x * Real.cos s.z) / (sphericalToCartesian s).length) = s.z
    rw [spherical_length, abs_of_pos hr]
    rw [mul_div_cancel_left₀ (Real.cos s.z) hr.ne']
    exact Real.arccos_cos ht.1.le ht.2.le

--ai: noncanonical spherical azimuths wrap rather than round-trip as raw real angles.
theorem spherical_azimuth_wrapped (s : F32v3) (hr : 0 < s.x)
    (ht : s.z ∈ Set.Ioo 0 Real.pi) :
    (cartesianToSpherical (sphericalToCartesian s)).y =
      toIocMod Real.two_pi_pos (-Real.pi) s.y := by
  change Complex.arg (xy (sphericalToCartesian s)) = _
  rw [← spherical_cylinder_cartesian, xy_cylinder]
  have hp := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, sphericalToCylinder] using
    Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hp s.y

--ai: the direct spherical/cylindrical helpers also recover absolute spherical radius.
theorem spherical_cylinder_radius (s : F32v3) :
    (cylinderToSpherical (sphericalToCylinder s)).x = |s.x| := by
  change Real.sqrt ((s.x * Real.sin s.z) * (s.x * Real.sin s.z) +
    (s.x * Real.cos s.z) * (s.x * Real.cos s.z)) = |s.x|
  have h : (s.x * Real.sin s.z) * (s.x * Real.sin s.z) +
      (s.x * Real.cos s.z) * (s.x * Real.cos s.z) = s.x ^ 2 := by
    ring_nf
    simp only [Real.cos_sq']
    ring
  rw [h, Real.sqrt_sq_eq_abs]

--ai: direct conversion preserves the stored azimuth even at poles, unlike a Cartesian detour.
theorem spherical_cylinder_spherical (s : F32v3) (hr : 0 < s.x)
    (ht : s.z ∈ Set.Icc 0 Real.pi) :
    cylinderToSpherical (sphericalToCylinder s) = s := by
  have hrad := (spherical_cylinder_radius s).trans (abs_of_pos hr)
  ext
  · exact hrad
  · rfl
  · change Real.arccos ((s.x * Real.cos s.z) /
      (cylinderToSpherical (sphericalToCylinder s)).x) = s.z
    rw [hrad, mul_div_cancel_left₀ (Real.cos s.z) hr.ne']
    exact Real.arccos_cos ht.1 ht.2

--ai: planar radial square plus axial square is the full squared radius.
theorem radius_decomposition (p : F32v3) :
    p.length ^ 2 = planarRadius p ^ 2 + p.z ^ 2 := by
  rw [F32v3.length_sq]
  unfold planarRadius
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg p.x, sq_nonneg p.y])]
  unfold F32v3.lengthSqr
  ring

--ai: acos receives an in-domain axial ratio when the spherical radius is positive.
theorem axial_ratio_bounds (p : F32v3) (hr : 0 < p.length) :
    -1 ≤ p.z / p.length ∧ p.z / p.length ≤ 1 := by
  have h := radius_decomposition p
  have hz : |p.z| ≤ p.length := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (planarRadius p)]) hr.le
  constructor
  · apply (le_div_iff₀ hr).mpr
    linarith [(abs_le.mp hz).1]
  · apply (div_le_iff₀ hr).mpr
    linarith [(abs_le.mp hz).2]

--ai: exact inclination cosine reconstructs the axial coordinate.
theorem inclination_axial (p : F32v3) (hr : 0 < p.length) :
    p.length * Real.cos (Real.arccos (p.z / p.length)) = p.z := by
  rw [Real.cos_arccos (axial_ratio_bounds p hr).1 (axial_ratio_bounds p hr).2]
  field_simp

--ai: nonnegative inclination sine reconstructs planar radius, including a nonzero pole.
theorem inclination_planar (p : F32v3) (hr : 0 < p.length) :
    p.length * Real.sin (Real.arccos (p.z / p.length)) = planarRadius p := by
  have hs : 0 ≤ Real.sin (Real.arccos (p.z / p.length)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hz := inclination_axial p hr
  have ht := Real.sin_sq_add_cos_sq (Real.arccos (p.z / p.length))
  have hd := radius_decomposition p
  have hscaled := congrArg (fun t : ℝ => p.length ^ 2 * t) ht
  have haxial := congrArg (fun t : ℝ => t ^ 2) hz
  apply (sq_eq_sq₀ (mul_nonneg hr.le hs) (Real.sqrt_nonneg _)).mp
  change (p.length * Real.sin (Real.arccos (p.z / p.length))) ^ 2 = planarRadius p ^ 2
  nlinarith only [hscaled, haxial, hd]

--ai: Cartesian spherical reconstruction excludes the C origin singularity but includes nonzero poles.
theorem cartesian_spherical_cartesian (p : F32v3) (hr : 0 < p.length) :
    sphericalToCartesian (cartesianToSpherical p) = p := by
  have hx := Complex.norm_mul_cos_arg (xy p)
  have hy := Complex.norm_mul_sin_arg (xy p)
  rw [xy_norm] at hx hy
  ext
  · change (p.length * Real.sin (Real.arccos (p.z / p.length))) * Real.cos (Complex.arg (xy p)) = p.x
    rw [inclination_planar p hr]
    exact hx
  · change (p.length * Real.sin (Real.arccos (p.z / p.length))) * Real.sin (Complex.arg (xy p)) = p.y
    rw [inclination_planar p hr]
    exact hy
  · exact inclination_axial p hr

--ai: reverse direct conversion needs nonnegative cylindrical radius and nonzero total radius.
theorem cylinder_spherical_cylinder (c : F32v3) (hc : 0 ≤ c.x)
    (hr : 0 < Real.sqrt (c.x * c.x + c.z * c.z)) :
    sphericalToCylinder (cylinderToSpherical c) = c := by
  have hp : (F32v3.mk c.x 0 c.z).length = Real.sqrt (c.x * c.x + c.z * c.z) := by
    simp [F32v3.length, F32v3.lengthSqr]
  have hpos : 0 < (F32v3.mk c.x 0 c.z).length := by rw [hp]; exact hr
  have hx := inclination_planar (F32v3.mk c.x 0 c.z) hpos
  have hz := inclination_axial (F32v3.mk c.x 0 c.z) hpos
  rw [hp] at hx hz
  have hplanar : planarRadius (F32v3.mk c.x 0 c.z) = c.x := by
    simp [planarRadius, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  rw [hplanar] at hx
  ext
  · exact hx
  · rfl
  · exact hz

--ai: zero cylindrical radius erases azimuth, independently of the height.
theorem cylinder_zero_radius (azimuth height : ℝ) :
    cylinderToCartesian ⟨0, azimuth, height⟩ = ⟨0, 0, height⟩ := by
  simp [cylinderToCartesian]

--ai: zero spherical radius erases both angles; no Cartesian-to-spherical C origin value is asserted.
theorem spherical_zero_radius (azimuth inclination : ℝ) :
    sphericalToCartesian ⟨0, azimuth, inclination⟩ = F32v3.zero := by
  simp [sphericalToCartesian, F32v3.zero]

--ai: the ideal atan2 model chooses zero azimuth on the cylindrical axis, not a signed-zero C branch.
theorem cylindrical_axis (height : ℝ) :
    cartesianToCylinder ⟨0, 0, height⟩ = ⟨0, 0, height⟩ := by
  simp [cartesianToCylinder, planarRadius, xy]
  exact Complex.arg_zero

--ai: azimuth is lost at the north pole regardless of its supplied value.
theorem spherical_north_pole (radius azimuth : ℝ) :
    sphericalToCartesian ⟨radius, azimuth, 0⟩ = ⟨0, 0, radius⟩ := by
  simp [sphericalToCartesian]

--ai: azimuth is likewise lost at the south pole; inclination is measured from +z.
theorem spherical_south_pole (radius azimuth : ℝ) :
    sphericalToCartesian ⟨radius, azimuth, Real.pi⟩ = ⟨0, 0, -radius⟩ := by
  simp [sphericalToCartesian]

end GxMath.Coordinates
