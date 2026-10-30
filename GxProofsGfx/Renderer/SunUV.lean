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
  gX — Sun UV Projection Pipeline

  Salvaged from gameX lean/GameXProofs/SunUVProof.lean, re-verified
  line by line against src/renderer/gfx/sun_uv.c
  (gX_RendererGFX_GetSunScreenUV):
    1. sunDir = -sun.dir                          (sun_uv.c:44)
    2. sunView = view × sunDir, translation × 0   (sun_uv.c:52-55)
    3. sunClip = proj × sunView                   (sun_uv.c:58-61)
    4. behind = (sunClip.w ≤ 0)                   (sun_uv.c:63)
    5. ndc = sunClip / sunClip.w                  (sun_uv.c:68)
    6. uv  = (ndc + 1) / 2                        (sun_uv.c:70)
    7. sequential clamps to [0,1]                 (sun_uv.c:72-75)

  Verified identities over ℝ:
    - view transform ignores the translation column for directions
    - NDC→UV mapping: ndc = -1 → uv = 0, ndc = +1 → uv = 1,
      ndc = 0 → uv = 1/2 (screen center)
    - NDC→UV is strictly increasing (monotone screen position)
    - clamp01 keeps values inside [0,1]
    - clamp01 is the identity on [0,1]
    - clamp01 is idempotent (clamp(clamp(x)) = clamp(x))

  Theorems proven: 10
    - view_transform_no_translation: direction transforms drop translation terms
    - ndc_to_uv_neg_one:     ndc -1 → uv 0
    - ndc_to_uv_zero:        ndc 0 → uv 1/2
    - ndc_to_uv_one:         ndc +1 → uv 1
    - ndc_to_uv_increasing:  ndc1 < ndc2 → uv1 < uv2
    - clamp01_in_bounds:     clamp01 x ∈ [0,1]
    - clamp01_identity:      x ∈ [0,1] → clamp01 x = x
    - clamp01_idempotent:    clamp01 (clamp01 x) = clamp01 x
    - clamp01_below:         x ≤ 0 → clamp01 x = 0
    - clamp01_above:         1 ≤ x → clamp01 x = 1
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.SunUV

@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

@[ext]
structure Vec4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

@[ext]
structure Matrix4 where
  m0  : ℝ
  m1  : ℝ
  m2  : ℝ
  m3  : ℝ
  m4  : ℝ
  m5  : ℝ
  m6  : ℝ
  m7  : ℝ
  m8  : ℝ
  m9  : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m13 : ℝ
  m14 : ℝ
  m15 : ℝ

-- View transform (sun_uv.c:52-55): column access. Direction vectors (w=0)
-- drop the translation column.
def viewTransform (view : Matrix4) (v : Vec3) : Vec4 :=
  { x := view.m0*v.x + view.m4*v.y + view.m8*v.z
  , y := view.m1*v.x + view.m5*v.y + view.m9*v.z
  , z := view.m2*v.x + view.m6*v.y + view.m10*v.z
  , w := view.m3*v.x + view.m7*v.y + view.m11*v.z
  }

-- Clip transform (sun_uv.c:58-61)
def clipTransform (proj : Matrix4) (v : Vec4) : Vec4 :=
  { x := proj.m0*v.x + proj.m4*v.y + proj.m8*v.z + proj.m12*v.w
  , y := proj.m1*v.x + proj.m5*v.y + proj.m9*v.z + proj.m13*v.w
  , z := proj.m2*v.x + proj.m6*v.y + proj.m10*v.z + proj.m14*v.w
  , w := proj.m3*v.x + proj.m7*v.y + proj.m11*v.z + proj.m15*v.w
  }

-- Full projection
def project (view proj : Matrix4) (sunDir : Vec3) : Vec4 :=
  clipTransform proj (viewTransform view sunDir)

-- The C code writes `view.m12 * 0.0f` explicitly: the translation column
-- (m12..m15) is multiplied by the direction's w = 0, so it contributes
-- nothing. The definition above already drops it; this theorem records
-- the equivalence with the explicit form.
theorem view_transform_no_translation (view : Matrix4) (d : Vec3) :
    viewTransform view d =
      { x := view.m0*d.x + view.m4*d.y + view.m8*d.z + view.m12*0
      , y := view.m1*d.x + view.m5*d.y + view.m9*d.z + view.m13*0
      , z := view.m2*d.x + view.m6*d.y + view.m10*d.z + view.m14*0
      , w := view.m3*d.x + view.m7*d.y + view.m11*d.z + view.m15*0
      } := by
  ext <;> simp [viewTransform] <;> ring

-- NDC → UV (sun_uv.c:70)
noncomputable def ndcToUV (x : ℝ) : ℝ := (x + 1) / 2

theorem ndc_to_uv_neg_one : ndcToUV (-1) = 0 := by
  unfold ndcToUV
  norm_num

theorem ndc_to_uv_zero : ndcToUV 0 = 1 / 2 := by
  unfold ndcToUV
  norm_num

theorem ndc_to_uv_one : ndcToUV 1 = 1 := by
  unfold ndcToUV
  norm_num

-- NDC→UV is strictly increasing: screen-space order is preserved.
theorem ndc_to_uv_increasing {a b : ℝ} (h : a < b) : ndcToUV a < ndcToUV b := by
  unfold ndcToUV
  linarith

-- UV clamping (sun_uv.c:72-75): sequential if-clamps.
noncomputable def clamp01 (x : ℝ) : ℝ := if x < 0 then 0 else if 1 < x then 1 else x

-- clamp01 always returns a value inside [0,1].
theorem clamp01_in_bounds (x : ℝ) : 0 ≤ clamp01 x ∧ clamp01 x ≤ 1 := by
  unfold clamp01
  by_cases h0 : x < 0
  · simp [h0]
  · by_cases h1 : 1 < x
    · simp [h0, h1]
    · have hge : 0 ≤ x := by linarith
      have hle : x ≤ 1 := by linarith
      simp [h0, h1, hge, hle]

-- clamp01 is the identity on [0,1].
theorem clamp01_identity {x : ℝ} (hlo : 0 ≤ x) (hhi : x ≤ 1) : clamp01 x = x := by
  unfold clamp01
  have hnot0 : ¬ x < 0 := by linarith
  have hnot1 : ¬ 1 < x := by linarith
  simp [hnot0, hnot1]

-- clamp01 is idempotent.
theorem clamp01_idempotent (x : ℝ) : clamp01 (clamp01 x) = clamp01 x := by
  have hb := clamp01_in_bounds x
  exact clamp01_identity hb.1 hb.2

-- Values ≤ 0 clamp to 0.
theorem clamp01_below {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  unfold clamp01
  by_cases h0 : x < 0
  · simp [h0]
  · have hx0 : x = 0 := by linarith
    have hnot1 : ¬ 1 < x := by linarith
    simp [h0, hnot1, hx0]

-- Values ≥ 1 clamp to 1.
theorem clamp01_above {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01
  have hnot0 : ¬ x < 0 := by linarith
  by_cases h1 : 1 < x
  · simp [hnot0, h1]
  · have hx1 : x = 1 := by linarith
    simp [hnot0, h1, hx1]

end GxProofsGfx.SunUV
