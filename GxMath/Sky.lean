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
  gX — Cartesian sky-frame contracts for src/gxmath/convert.c.
  //ai: exact-real trigonometry with angles in radians.

  Obliquity is arbitrary here; C supplies 23.4f * gX_DEG2RAD. Observer
  latitude/longitude are parameters in both directions. The horizontal
  mapping is orthogonal but reverses handedness; its signs are intentional.
  No IEEE sin/cos error, degree-constant accuracy, angular-coordinate branch
  convention, physical-observer validation or GPU behavior is certified.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import GxMath.Vector

namespace GxMath.Sky

--ai: parameterized version of the shipped equatorial-to-ecliptic formula.
noncomputable def equatorialToEcliptic (p : F32v3) (obliquity : ℝ) : F32v3 :=
  let ce := Real.cos obliquity
  let se := Real.sin obliquity
  { x := p.x, y := p.y * ce + p.z * se, z := p.z * ce - p.y * se }

--ai: inverse ecliptic frame with the same obliquity parameter.
noncomputable def eclipticToEquatorial (p : F32v3) (obliquity : ℝ) : F32v3 :=
  let ce := Real.cos obliquity
  let se := Real.sin obliquity
  { x := p.x, y := p.y * ce - p.z * se, z := p.z * ce + p.y * se }

--ai: preserve the native horizontal axes, including the handedness reversal.
noncomputable def equatorialToHorizontal (p : F32v3) (latitude longitude : ℝ) : F32v3 :=
  let sinLat := Real.sin latitude
  let cosLat := Real.cos latitude
  let sinLon := Real.sin longitude
  let cosLon := Real.cos longitude
  { x := p.x * sinLat * cosLon + p.y * sinLat * sinLon - p.z * cosLat
    y := p.x * sinLon - p.y * cosLon
    z := p.x * cosLat * cosLon + p.y * cosLat * sinLon + p.z * sinLat }

--ai: inverse horizontal mapping, not a second independently chosen convention.
noncomputable def horizontalToEquatorial (p : F32v3) (latitude longitude : ℝ) : F32v3 :=
  let sinLat := Real.sin latitude
  let cosLat := Real.cos latitude
  let sinLon := Real.sin longitude
  let cosLon := Real.cos longitude
  { x := p.x * sinLat * cosLon + p.z * cosLat * cosLon + p.y * sinLon
    y := p.x * sinLat * sinLon + p.z * cosLat * sinLon - p.y * cosLon
    z := p.z * sinLat - p.x * cosLat }

--ai: both ecliptic round trips hold for every Cartesian vector and real angle.
theorem equatorial_ecliptic_equatorial (p : F32v3) (obliquity : ℝ) :
    eclipticToEquatorial (equatorialToEcliptic p obliquity) obliquity = p := by
  ext <;> dsimp [equatorialToEcliptic, eclipticToEquatorial] <;>
    ring_nf <;> simp only [Real.cos_sq'] <;> ring

--ai: the reverse ecliptic round trip uses the same observer-independent angle.
theorem ecliptic_equatorial_ecliptic (p : F32v3) (obliquity : ℝ) :
    equatorialToEcliptic (eclipticToEquatorial p obliquity) obliquity = p := by
  ext <;> dsimp [equatorialToEcliptic, eclipticToEquatorial] <;>
    ring_nf <;> simp only [Real.cos_sq'] <;> ring

--ai: both horizontal round trips retain the observer's latitude and longitude.
theorem equatorial_horizontal_equatorial (p : F32v3) (latitude longitude : ℝ) :
    horizontalToEquatorial (equatorialToHorizontal p latitude longitude) latitude longitude = p := by
  ext <;> dsimp [equatorialToHorizontal, horizontalToEquatorial] <;>
    ring_nf <;> simp only [Real.cos_sq'] <;> ring

--ai: horizontal vectors need not be unit length or nonzero for this identity.
theorem horizontal_equatorial_horizontal (p : F32v3) (latitude longitude : ℝ) :
    equatorialToHorizontal (horizontalToEquatorial p latitude longitude) latitude longitude = p := by
  ext <;> dsimp [equatorialToHorizontal, horizontalToEquatorial] <;>
    ring_nf <;> simp only [Real.cos_sq'] <;> ring

--ai: squared-length preservation follows directly from exact trig identities.
theorem equatorial_ecliptic_lengthSqr (p : F32v3) (obliquity : ℝ) :
    (equatorialToEcliptic p obliquity).lengthSqr = p.lengthSqr := by
  dsimp [equatorialToEcliptic, F32v3.lengthSqr]
  ring_nf
  simp only [Real.cos_sq']
  ring

--ai: the inverse ecliptic transform also preserves squared length.
theorem ecliptic_equatorial_lengthSqr (p : F32v3) (obliquity : ℝ) :
    (eclipticToEquatorial p obliquity).lengthSqr = p.lengthSqr := by
  dsimp [eclipticToEquatorial, F32v3.lengthSqr]
  ring_nf
  simp only [Real.cos_sq']
  ring

--ai: observer angles do not change vector magnitude in the horizontal frame.
theorem equatorial_horizontal_lengthSqr (p : F32v3) (latitude longitude : ℝ) :
    (equatorialToHorizontal p latitude longitude).lengthSqr = p.lengthSqr := by
  dsimp [equatorialToHorizontal, F32v3.lengthSqr]
  ring_nf
  simp only [Real.cos_sq']
  ring

--ai: the inverse horizontal transform preserves squared length for all inputs.
theorem horizontal_equatorial_lengthSqr (p : F32v3) (latitude longitude : ℝ) :
    (horizontalToEquatorial p latitude longitude).lengthSqr = p.lengthSqr := by
  dsimp [horizontalToEquatorial, F32v3.lengthSqr]
  ring_nf
  simp only [Real.cos_sq']
  ring

--ai: these magnitude results concern the exact square-root model, not sqrtf.
theorem equatorial_ecliptic_length (p : F32v3) (obliquity : ℝ) :
    (equatorialToEcliptic p obliquity).length = p.length := by
  unfold F32v3.length
  rw [equatorial_ecliptic_lengthSqr]

--ai: length preservation in the reverse ecliptic direction.
theorem ecliptic_equatorial_length (p : F32v3) (obliquity : ℝ) :
    (eclipticToEquatorial p obliquity).length = p.length := by
  unfold F32v3.length
  rw [ecliptic_equatorial_lengthSqr]

--ai: length preservation in the observer-parameterized horizontal direction.
theorem equatorial_horizontal_length (p : F32v3) (latitude longitude : ℝ) :
    (equatorialToHorizontal p latitude longitude).length = p.length := by
  unfold F32v3.length
  rw [equatorial_horizontal_lengthSqr]

--ai: length preservation in the reverse horizontal direction.
theorem horizontal_equatorial_length (p : F32v3) (latitude longitude : ℝ) :
    (horizontalToEquatorial p latitude longitude).length = p.length := by
  unfold F32v3.length
  rw [horizontal_equatorial_lengthSqr]

--ai: the ecliptic transform is orientation-preserving.
theorem ecliptic_orientation (obliquity : ℝ) :
    ((equatorialToEcliptic F32v3.unitX obliquity).cross
      (equatorialToEcliptic F32v3.unitY obliquity)).dot
      (equatorialToEcliptic F32v3.unitZ obliquity) = 1 := by
  dsimp [equatorialToEcliptic, F32v3.unitX, F32v3.unitY, F32v3.unitZ, F32v3.cross, F32v3.dot]
  ring_nf
  simp only [Real.cos_sq']
  ring

--ai: explicitly pin the native horizontal frame's negative orientation.
theorem horizontal_orientation (latitude longitude : ℝ) :
    ((equatorialToHorizontal F32v3.unitX latitude longitude).cross
      (equatorialToHorizontal F32v3.unitY latitude longitude)).dot
      (equatorialToHorizontal F32v3.unitZ latitude longitude) = -1 := by
  dsimp [equatorialToHorizontal, F32v3.unitX, F32v3.unitY, F32v3.unitZ, F32v3.cross, F32v3.dot]
  ring_nf
  simp only [Real.cos_sq']
  ring

end GxMath.Sky
