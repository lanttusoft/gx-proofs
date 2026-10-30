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
  gX — Behind-Camera Detection

  Salvaged from gameX lean/GameXProofs/BehindCamera.lean, re-verified:
  the behind condition (clip-space w ≤ 0 after view-projection) matches
  src/renderer/gfx/sun_uv.c:63, which gates both the godray and
  lensflare passes (godray.c, lensflare.c:66).

  For a direction vector (w=0 in view space), the clip-space w
  is computed from the third row of the combined projection·view
  matrix dotted with the direction.

  Math is modeled over ℝ. The core geometric facts proven:
    - dot is symmetric, dot(v,v) ≥ 0, and positive definite
    - for unit vectors, dot u v = cos(angle); the sun is in front iff
      the angle is acute (dot > 0), behind iff obtuse (dot < 0)

  Theorems proven: 8
    - sun_dir_from_is_neg:   sunDirFrom negates the sun direction
    - dot_comm:              dot is symmetric
    - dot_self_nonneg:       dot(v, v) ≥ 0
    - dot_self_zero_iff_zero: dot(v, v) = 0 ↔ v = 0
    - cos_of_angle:          cos(arccos x) = x for |x| ≤ 1
    - dot_unit_abs_le_one:   Cauchy-Schwarz for unit vectors
    - in_front_iff_acute:    dot u v > 0 ↔ angle < 90° (unit u, v)
    - behind_iff_obtuse:     dot u v < 0 ↔ angle > 90° (unit u, v)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace GxProofsGfx.BehindCamera

@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot (a b : Vec3) : ℝ := a.x*b.x + a.y*b.y + a.z*b.z

def zero : Vec3 := { x := 0, y := 0, z := 0 }

-- Camera forward direction: target - position (not yet normalized)
def cameraForward (camPos camTarget : Vec3) : Vec3 :=
  { x := camTarget.x - camPos.x
  , y := camTarget.y - camPos.y
  , z := camTarget.z - camPos.z
  }

-- Sun direction FROM scene TOWARD sun: -sun.dir (sun_uv.c:44)
def sunDirFrom (sunDir : Vec3) : Vec3 :=
  { x := -sunDir.x, y := -sunDir.y, z := -sunDir.z }

theorem sun_dir_from_is_neg (sunDir : Vec3) :
    sunDirFrom sunDir = { x := -sunDir.x, y := -sunDir.y, z := -sunDir.z } := rfl

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  ring

-- dot(v, v) = |v|² ≥ 0 — squared length is non-negative.
theorem dot_self_nonneg (v : Vec3) : 0 ≤ dot v v := by
  have hx : 0 ≤ v.x * v.x := mul_self_nonneg v.x
  have hy : 0 ≤ v.y * v.y := mul_self_nonneg v.y
  have hz : 0 ≤ v.z * v.z := mul_self_nonneg v.z
  unfold dot
  nlinarith

-- Positive definite: dot(v, v) = 0 iff v is the zero vector.
theorem dot_self_zero_iff_zero (v : Vec3) : dot v v = 0 ↔ v = zero := by
  constructor
  · intro h
    have hx0 : v.x = 0 := by
      have hx : 0 ≤ v.x * v.x := mul_self_nonneg v.x
      have hy : 0 ≤ v.y * v.y := mul_self_nonneg v.y
      have hz : 0 ≤ v.z * v.z := mul_self_nonneg v.z
      unfold dot at h
      have hx2 : v.x * v.x = 0 := by nlinarith
      exact mul_self_eq_zero.mp hx2
    have hy0 : v.y = 0 := by
      have hx : 0 ≤ v.x * v.x := mul_self_nonneg v.x
      have hy : 0 ≤ v.y * v.y := mul_self_nonneg v.y
      have hz : 0 ≤ v.z * v.z := mul_self_nonneg v.z
      unfold dot at h
      have hy2 : v.y * v.y = 0 := by nlinarith
      exact mul_self_eq_zero.mp hy2
    have hz0 : v.z = 0 := by
      have hx : 0 ≤ v.x * v.x := mul_self_nonneg v.x
      have hy : 0 ≤ v.y * v.y := mul_self_nonneg v.y
      have hz : 0 ≤ v.z * v.z := mul_self_nonneg v.z
      unfold dot at h
      have hz2 : v.z * v.z = 0 := by nlinarith
      exact mul_self_eq_zero.mp hz2
    ext <;> simp [zero, hx0, hy0, hz0]
  · intro hv
    subst hv
    simp [dot, zero]

-- cos(arccos x) = x whenever |x| ≤ 1.
theorem cos_of_angle {x : ℝ} (h : |x| ≤ 1) : Real.cos (Real.arccos x) = x := by
  exact Real.cos_arccos (abs_le.mp h).1 (abs_le.mp h).2

-- Cauchy-Schwarz for the dot product: |u · v| ≤ |u| |v|.
-- For unit vectors this reduces to |u · v| ≤ 1.
theorem dot_unit_abs_le_one {u v : Vec3} (hu : dot u u = 1) (hv : dot v v = 1) :
    |dot u v| ≤ 1 := by
  -- Lagrange identity: (u·v)² + |u×v|² = |u|²|v|², so (u·v)² ≤ |u|²|v|² = 1.
  have hcross : 0 ≤ (u.y*v.z - u.z*v.y)^2 + (u.z*v.x - u.x*v.z)^2 + (u.x*v.y - u.y*v.x)^2 := by
    positivity
  have hidentity : (dot u u) * (dot v v) - (dot u v)^2 =
      (u.y*v.z - u.z*v.y)^2 + (u.z*v.x - u.x*v.z)^2 + (u.x*v.y - u.y*v.x)^2 := by
    unfold dot
    ring
  have hsq : (dot u v)^2 ≤ (dot u u) * (dot v v) := by
    nlinarith
  rw [hu, hv] at hsq
  have hsq' : (dot u v)^2 ≤ 1 := by simpa [one_mul] using hsq
  exact (sq_le_one_iff_abs_le_one (dot u v)).mp hsq'

-- In front iff acute: for unit u, v, dot u v > 0 ↔ angle < 90°.
theorem in_front_iff_acute {u v : Vec3} (hu : dot u u = 1) (hv : dot v v = 1) :
    dot u v > 0 ↔ Real.arccos (dot u v) < Real.pi / 2 := by
  constructor
  · intro hpos
    have h1 : |dot u v| ≤ 1 := dot_unit_abs_le_one hu hv
    -- arccos strictly decreasing: 0 < x → arccos x < arccos 0 = π/2
    have hlt : Real.arccos (dot u v) < Real.arccos 0 :=
      Real.arccos_lt_arccos (by norm_num) hpos (abs_le.mp h1).2
    rwa [Real.arccos_zero] at hlt
  · intro hang
    have h1 : |dot u v| ≤ 1 := dot_unit_abs_le_one hu hv
    -- contrapositive: if dot ≤ 0 then arccos 0 ≤ arccos(dot), contradicting hang
    have hpos : 0 < dot u v := by
      by_contra hnot
      have hle : dot u v ≤ 0 := le_of_not_gt hnot
      have hge : Real.arccos 0 ≤ Real.arccos (dot u v) :=
        Real.arccos_le_arccos hle
      rw [Real.arccos_zero] at hge
      linarith
    exact hpos

-- Behind iff obtuse: for unit u, v, dot u v < 0 ↔ angle > 90°.
theorem behind_iff_obtuse {u v : Vec3} (hu : dot u u = 1) (hv : dot v v = 1) :
    dot u v < 0 ↔ Real.pi / 2 < Real.arccos (dot u v) := by
  constructor
  · intro hneg
    have h1 : |dot u v| ≤ 1 := dot_unit_abs_le_one hu hv
    -- arccos strictly decreasing: x < 0 → arccos 0 < arccos x
    have hlt : Real.arccos 0 < Real.arccos (dot u v) :=
      Real.arccos_lt_arccos (abs_le.mp h1).1 hneg (by norm_num)
    rwa [Real.arccos_zero] at hlt
  · intro hang
    have h1 : |dot u v| ≤ 1 := dot_unit_abs_le_one hu hv
    -- contrapositive: if 0 ≤ dot then arccos(dot) ≤ arccos 0, contradicting hang
    have hneg : dot u v < 0 := by
      by_contra hnot
      have hge : 0 ≤ dot u v := le_of_not_gt hnot
      have hle : Real.arccos (dot u v) ≤ Real.arccos 0 :=
        Real.arccos_le_arccos hge
      rw [Real.arccos_zero] at hle
      linarith
    exact hneg

end GxProofsGfx.BehindCamera
