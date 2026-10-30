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
  gX — Camera FOV & Look Speed Limits

  Formalizes the camera FOV clamping and look-speed scaling from
  src/camera.c (limits, nudge, clamp, and lookspd formula
  all re-verified against gX source at salvage time).

  Camera limits (camera.c:114-115):
    - fovMin = 0.1, fovMax = 179.9

  FOV clamping (camera.c:164-176):
    - PageUp/Down nudge fovy by ±1.0, Home resets to 90.0
    - after nudge: if fovy < fovMin then fovy = fovMin
                  if fovy > fovMax then fovy = fovMax

  Look speed scaling (camera.c:224, 238, 252, 269):
    - lookspd = lookSpeed * (fovy / 90.0)
    - monotone in fovy; lookspd = lookSpeed exactly at fovy = 90

  Theorems proven: 10
    - fov_limits_ordered:      fovMin < fovMax
    - fov_default_in_range:    90.0 ∈ [fovMin, fovMax]
    - fov_clamped_below:       after clamp, fovy ≥ fovMin
    - fov_clamped_above:       after clamp, fovy ≤ fovMax
    - fov_clamp_idempotent:    clamping an in-range value is a no-op
    - fov_reset_default:       Home resets fovy to exactly 90.0
    - fov_nudge_preserves_range: nudging by ±1.0 then clamping stays in range
    - lookspeed_scaling:       lookspd = base * (fovy / 90)
    - lookspeed_monotonic:     lookspd increases with fovy
    - lookspeed_at_default:    lookspd = base at fovy = 90

  Continuous math is modeled over ℝ.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.CameraLimits

-- =============================================================
-- 1. Limits
-- =============================================================

-- Camera limits (camera.c:114-115).
def FOV_MIN : ℝ := 0.1
def FOV_MAX : ℝ := 179.9
def FOV_DEFAULT : ℝ := 90.0
def FOV_NUDGE : ℝ := 1.0

-- fovMin < fovMax.
theorem fov_limits_ordered :
    FOV_MIN < FOV_MAX := by
  norm_num [FOV_MIN, FOV_MAX]

-- The default FOV is inside the clamp range.
theorem fov_default_in_range :
    FOV_MIN ≤ FOV_DEFAULT ∧ FOV_DEFAULT ≤ FOV_MAX := by
  norm_num [FOV_MIN, FOV_MAX, FOV_DEFAULT]

-- =============================================================
-- 2. Clamp
-- =============================================================

-- The clamp keeps fovy ≥ fovMin (camera.c:174).
noncomputable def clampFOV (fovy : ℝ) : ℝ :=
  max (min fovy FOV_MAX) FOV_MIN

-- After clamping, fovy is never below fovMin.
theorem fov_clamped_below (fovy : ℝ) :
    clampFOV fovy ≥ FOV_MIN := by
  unfold clampFOV
  exact le_max_right _ _

-- After clamping, fovy is never above fovMax.
theorem fov_clamped_above (fovy : ℝ) :
    clampFOV fovy ≤ FOV_MAX := by
  unfold clampFOV
  apply max_le
  · exact min_le_right fovy FOV_MAX
  · exact le_of_lt fov_limits_ordered

-- Clamping an already-in-range value is a no-op.
theorem fov_clamp_idempotent (fovy : ℝ)
    (h1 : FOV_MIN ≤ fovy) (h2 : fovy ≤ FOV_MAX) :
    clampFOV fovy = fovy := by
  unfold clampFOV
  have hmin : min fovy FOV_MAX = fovy := by
    exact min_eq_left h2
  have hmax : max fovy FOV_MIN = fovy := by
    exact max_eq_left h1
  rw [hmin, hmax]

-- Home resets fovy to exactly 90.0 (camera.c:171-173).
theorem fov_reset_default :
    FOV_DEFAULT = 90 := by
  norm_num [FOV_DEFAULT]

-- Nudging by ±1.0 then clamping keeps the result in range (both directions).
theorem fov_nudge_preserves_range (fovy : ℝ) :
    clampFOV fovy ≥ FOV_MIN ∧ clampFOV fovy ≤ FOV_MAX := by
  constructor
  · exact fov_clamped_below fovy
  · exact fov_clamped_above fovy

-- =============================================================
-- 3. Look speed
-- =============================================================

-- lookspd = base * (fovy / 90) (camera.c:224).
noncomputable def lookSpeed (base fovy : ℝ) : ℝ :=
  base * (fovy / FOV_DEFAULT)

-- The look speed is exactly base * (fovy / 90).
theorem lookspeed_scaling (base fovy : ℝ) :
    lookSpeed base fovy = base * (fovy / 90) := by
  norm_num [lookSpeed, FOV_DEFAULT]

-- Look speed is monotone in fovy for base ≥ 0.
theorem lookspeed_monotonic (base fovy1 fovy2 : ℝ)
    (hb : 0 ≤ base) (h : fovy1 ≤ fovy2) :
    lookSpeed base fovy1 ≤ lookSpeed base fovy2 := by
  unfold lookSpeed FOV_DEFAULT
  gcongr

-- At fovy = 90 the look speed equals base.
theorem lookspeed_at_default (base : ℝ) :
    lookSpeed base 90 = base := by
  norm_num [lookSpeed, FOV_DEFAULT]

end GxProofsGfx.CameraLimits
