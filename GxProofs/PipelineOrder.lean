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
  gX — GFX Pipeline Ordering

  Re-grounded successor to gameX lean/GameXProofs/PipelineOrder.lean.
  The gameX stage list (shadow < opaque < godrays < lensflare < bloom)
  went stale: gX runs bloom BEFORE godrays/lensflare and interposes a
  scene-copy pass. Re-verified against the actual call sequence in
  src/renderer/gfx/gfx_pipeline.c:
    Draw_Shadow (88) → Draw_Opaque (143) → scene_copy (261-288)
      → Bloom_Draw (295) → Godray_Draw (302) → LensFlare_Draw (307)
   This models relative labels for the selected six-stage projection, not the
   actual pass table, conditional dispatch, or omitted stages. SSAO and other
   producers must be checked separately against the current runtime sequence.
-/

namespace GxProofs.PipelineOrder

-- Stage indices as distinct constants
def STAGE_SHADOW     : Nat := 0
def STAGE_OPAQUE     : Nat := 1
def STAGE_SCENE_COPY : Nat := 2
def STAGE_BLOOM      : Nat := 3
def STAGE_GODRAYS    : Nat := 4
def STAGE_LENSFLARE  : Nat := 5

-- Order is sequential: 0 < 1 < 2 < 3 < 4 < 5
theorem shadow_before_opaque : STAGE_SHADOW < STAGE_OPAQUE := by
  unfold STAGE_SHADOW STAGE_OPAQUE; omega

theorem opaque_before_scene_copy : STAGE_OPAQUE < STAGE_SCENE_COPY := by
  unfold STAGE_OPAQUE STAGE_SCENE_COPY; omega

theorem scene_copy_before_bloom : STAGE_SCENE_COPY < STAGE_BLOOM := by
  unfold STAGE_SCENE_COPY STAGE_BLOOM; omega

theorem bloom_before_godrays : STAGE_BLOOM < STAGE_GODRAYS := by
  unfold STAGE_BLOOM STAGE_GODRAYS; omega

theorem godrays_before_lensflare : STAGE_GODRAYS < STAGE_LENSFLARE := by
  unfold STAGE_GODRAYS STAGE_LENSFLARE; omega

-- Transitive: all effects after opaque, lensflare is last of the six
theorem all_effects_after_opaque : STAGE_OPAQUE < STAGE_GODRAYS := by
  calc STAGE_OPAQUE < STAGE_BLOOM := by
          calc STAGE_OPAQUE < STAGE_SCENE_COPY := opaque_before_scene_copy
            _ < STAGE_BLOOM := scene_copy_before_bloom
    _ < STAGE_GODRAYS := bloom_before_godrays

theorem lensflare_is_last : STAGE_GODRAYS < STAGE_LENSFLARE ∧ STAGE_BLOOM < STAGE_LENSFLARE := by
  constructor
  · exact godrays_before_lensflare
  · calc STAGE_BLOOM < STAGE_GODRAYS := bloom_before_godrays
      _ < STAGE_LENSFLARE := godrays_before_lensflare

end GxProofs.PipelineOrder
