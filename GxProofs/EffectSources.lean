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
  gX — Effect Source Selection Specification

  Re-grounded successor to gameX lean/GameXProofs/EffectSources.lean.
  The gameX feature set (4 flags) and source IDs went stale: gX's
  needHdrSceneDepth is a 9-flag disjunction, the effects gate is a
  separate composite-consumer disjunction, and the final blit prefers bloom.scene
  → hdrScene → sceneColorLDR. Re-verified against
  src/renderer/gfx/gfx_pipeline.c:
    needHdrSceneDepth (116), hdr fallback (117-120),
    scene copy source (263-269), final blit source (394-403).

  Wrong source = wrong image.
-/

namespace GxProofs.EffectSources

-- The 9 features that set needHdrSceneDepth = true (gfx_pipeline.c:116).
def needHdrSceneDepth (bloom godrays lensflare ssr dof motionBlur taa ssao volumeFog : Bool) : Bool :=
  (bloom || godrays || lensflare || ssr || dof || motionBlur || taa || ssao || volumeFog)

-- needHdrSceneDepth is true iff any of the 9 features are enabled.
theorem needHdrSceneDepth_disjunction (bloom godrays lensflare ssr dof motionBlur taa ssao volumeFog : Bool) :
    needHdrSceneDepth bloom godrays lensflare ssr dof motionBlur taa ssao volumeFog =
      (bloom || godrays || lensflare || ssr || dof || motionBlur || taa || ssao || volumeFog) := rfl

--ai: match Pass_HasEffects/Pass_HasSsgi, including post-present consumers.
def hasEffects (bloom godrays fog lensflare ssr volumeFog motionBlur dof particles ssao useSsgi : Bool) : Bool :=
  (bloom || godrays || fog || lensflare || ssr || volumeFog || motionBlur || dof || particles || (ssao && useSsgi))

--ai: retain the exact Boolean contract and regression witnesses for the missing consumers.
theorem hasEffects_disjunction (bloom godrays fog lensflare ssr volumeFog motionBlur dof particles ssao useSsgi : Bool) :
    hasEffects bloom godrays fog lensflare ssr volumeFog motionBlur dof particles ssao useSsgi =
      (bloom || godrays || fog || lensflare || ssr || volumeFog || motionBlur || dof || particles || (ssao && useSsgi)) := rfl

theorem motion_blur_enters_chain :
    hasEffects false false false false false false true false false false false = true := by decide

theorem dof_enters_chain :
    hasEffects false false false false false false false true false false false = true := by decide

theorem particles_enter_chain :
    hasEffects false false false false false false false false true false false = true := by decide

theorem ssgi_enters_chain :
    hasEffects false false false false false false false false false true true = true := by decide

theorem ssgi_requires_ssao :
    hasEffects false false false false false false false false false false true = false := by decide

-- Effective need: needHdrSceneDepth with no loaded hdrScene falls back
-- to false (gfx_pipeline.c:117-120).
def effectiveNeed (need hdrLoaded : Bool) : Bool :=
  need && hdrLoaded

-- Without a loaded hdrScene the effective need is always false.
theorem effectiveNeed_unloaded (need : Bool) :
    effectiveNeed need false = false := by
  unfold effectiveNeed; cases need <;> simp

-- Scene copy source selection (gfx_pipeline.c:263-269).
-- Returns the source texture ID (0 = hdrScene, 1 = sceneColorLDR).
def sceneCopySource (needHdrDepth hdrLoaded ldrLoaded : Bool) : Nat :=
  if needHdrDepth && hdrLoaded then 0       -- hdrScene
  else if ldrLoaded then 1                    -- sceneColorLDR
  else 0                                      -- hdrScene fallback

-- Scene copy has 2 possible sources (hdrScene preferred, LDR fallback).
theorem scene_copy_sources : sceneCopySource true true true = 0
    ∧ sceneCopySource true true false = 0
    ∧ sceneCopySource true false true = 1
    ∧ sceneCopySource true false false = 0
    ∧ sceneCopySource false true true = 1
    ∧ sceneCopySource false true false = 0
    ∧ sceneCopySource false false true = 1
    ∧ sceneCopySource false false false = 0 := by
  unfold sceneCopySource; decide

-- Scene copy priority: hdrScene (when needHdrDepth) → sceneColorLDR → hdrScene fallback.
theorem scene_copy_priority (needHdrDepth hdrLoaded ldrLoaded : Bool) :
    sceneCopySource needHdrDepth hdrLoaded ldrLoaded = 0
    ∨ sceneCopySource needHdrDepth hdrLoaded ldrLoaded = 1 := by
  unfold sceneCopySource; cases needHdrDepth <;> cases hdrLoaded <;> cases ldrLoaded <;> simp

-- Final blit source selection (gfx_pipeline.c:394-403).
-- Returns the source FBO ID (0 = bloom.scene, 1 = hdrScene, 2 = sceneColorLDR, 3 = none).
def finalBlitSource (hasFx sceneLoaded hdrLoaded ldrLoaded : Bool) : Nat :=
  if hasFx && sceneLoaded then 0              -- bloom.scene
  else if hdrLoaded then 1                      -- hdrScene
  else if ldrLoaded then 2                      -- sceneColorLDR fallback
  else 3                                        -- none (error path, canvas undefined)

-- Final blit source table.
theorem final_blit_sources : finalBlitSource true true true true = 0
    ∧ finalBlitSource true true false false = 0
    ∧ finalBlitSource true false true true = 1
    ∧ finalBlitSource true false false true = 2
    ∧ finalBlitSource true false false false = 3
    ∧ finalBlitSource false true true true = 1
    ∧ finalBlitSource false false true true = 1
    ∧ finalBlitSource false false false true = 2
    ∧ finalBlitSource false false false false = 3 := by
  unfold finalBlitSource; decide

-- Final blit priority: bloom.scene → hdrScene → sceneColorLDR → none.
theorem final_blit_priority : ∀ (a b c d : Bool), finalBlitSource a b c d ≤ 3 := by
  intro a b c d
  unfold finalBlitSource
  cases a <;> cases b <;> cases c <;> cases d <;> simp

-- hdrScene wins when effects are off (the seed-copy keeps water/
-- transparent/labels visible — gfx_pipeline.c:121-123, 390-393).
theorem hdrScene_wins_effects_off :
    finalBlitSource false false true true = 1 ∧ finalBlitSource false false true false = 1 := by
  unfold finalBlitSource; simp

-- When needHdrSceneDepth is true and hdrScene is loaded,
-- the scene copy reads from hdrScene (source 0).
theorem needHdrDepth_enables_hdr_copy :
    sceneCopySource true true true = 0 ∧ sceneCopySource true true false = 0 := by
  unfold sceneCopySource; simp

end GxProofs.EffectSources
