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
  gX — Reflection Freshness Flag Protocol

  //ai: correspondence audit: legacy events below are abstract ghost flags,
  not a proof of GPU completion, per-pixel occupancy or numeric depth thresholds.
  planarDepthValid is NOT a C schema member; renderPlanar cannot certify all
  pixels contain geometry. auxSource/iblSource are simplified policies, NOT the
  full production routing. Source-grounded Boolean branch contracts follow at
  the end, including missing-mask legacy behavior and resource-availability gates.

  Pins the per-frame flag lifecycle from the reflection audit
  (src/renderer/gfx/draw.c: Draw_Reflections top,
  cubemap RenderEx site, Draw_SSR; consume gates in draw.c:1402,
  draw.c:1312, shader.c IBL fallback):
    - Every frame starts with planar + cube flags cleared (reset
      lives OUTSIDE the ENABLE_REFLECTIONS gate — disabling
      reflections mid-run must not leave stale-fresh flags).
    - Rendering a path sets its flag (planar fill, 6-face cubemap,
      SSR march); skipped paths stay cleared (drewThisFrame=false
      on the SSR skip path).
    - Consumers gate on the flags, never on sticky init state:
      planar aux needs filled, SSR env + IBL fallback need
      cube-fresh (else sky LUT / dummy cubemap).

  brown veil / dark tiles instead of mirror content. The depth texture is
  exclusive to the planar FBO (the wrapper-FBO clear never touches it),
  so it must be cleared in the planar pass or the mask reads
  everywhere-valid garbage.
  The planar clear color matches the scene bg (sky.color) so any
  unmasked empty pixel still reads as scene.

  Theorems proven: 11
    - reset_clears_all:      reset ⇒ no flag set
    - render_planar_sets:    planar render ⇒ planar fresh + depth valid
    - render_cube_sets:      cubemap render ⇒ cube fresh
    - render_ssr_sets:       SSR march ⇒ ssr drew
    - skip_keeps_cleared:    reset then skip ⇒ still cleared
    - planar_consume_gated:  planar consume ⇒ planar was fresh
    - planar_consume_depth:  planar consume ⇒ depth was valid
    - cube_consume_gated:    cube consume ⇒ cube was fresh
    - stale_falls_back:      no cube flag ⇒ dummy/sky-LUT fallback
    - empty_falls_to_env:    no depth ⇒ env fallback, never clear color
    - depth_cleared_far:     cleared depth reads far (below threshold fails)
  Bind-target theorems proven: 8 (sampler-target audit, v0.6.23+)
    - cube_slot_needs_cube:  map slot 7 (CUBEMAP) requires cube target
    - irr_slot_needs_cube:   map slot 8 (IRRADIANCE) requires cube target
    - pre_slot_needs_cube:   map slot 9 (PREFILTER) requires cube target
    - albedo_slot_needs_2d:  map slot 0 (ALBEDO) requires 2D target
    - mismatch_is_illegal:   cube texture bound as 2D is illegal
    - match_is_legal:        cube texture bound as cube is legal
    - illegal_adds_zero:     illegal bind ⇒ env term contributes zero
    - legal_passes:          legal bind ⇒ env term passes bias * sample
  Unit-parking theorems proven: 6 (CSM validation fix, v0.6.25+)
    - unparked_csm_collides_albedo: frame-1 regression pin
    - parked_csm_clean_albedo/normal/cube/shadow: dedicated unit
      shares with nothing of a different type
    - shared_2d_unit_ok:     same-type unit sharing stays legal
-/

namespace GxProofs.ReflectFlags

-- Per-frame freshness flags. planarDepthValid = the mirror depth
-- texture holds this frame's rasterized depth (cleared to far first);
-- the aux routes sample planar color only where it is set.
structure RFlags where
  planarFresh : Bool
  cubeFresh : Bool
  ssrDrew : Bool
  planarDepthValid : Bool

-- Frame-top reset (draw.c: Draw_Reflections head).
def reset : RFlags := { planarFresh := false, cubeFresh := false, ssrDrew := false, planarDepthValid := false }

-- Render events set their flag. The planar fill writes color + depth
-- together (depth cleared to far in the planar FBO first).
def renderPlanar (f : RFlags) : RFlags :=
  { f with planarFresh := true, planarDepthValid := true }
def renderCube (f : RFlags) : RFlags := { f with cubeFresh := true }
def renderSSR (f : RFlags) : RFlags := { f with ssrDrew := true }

-- Skip paths leave flags untouched.
def skip (f : RFlags) : RFlags := f

-- Consume gates (draw.c:1402 planar aux, draw.c:1312 SSR env,
-- shader.c IBL fallback, gfx_pipeline.c:317 SSR map).
def planarOk (f : RFlags) : Bool := f.planarFresh
def planarDepthOk (f : RFlags) : Bool := f.planarDepthValid
def cubeOk (f : RFlags) : Bool := f.cubeFresh
def ssrOk (f : RFlags) : Bool := f.ssrDrew

-- Aux-route decision (gfx_ssr.frag): planar color only when the fill
-- is fresh AND the mirror depth is valid; otherwise the env path.
inductive AuxSource where
  | planar
  | env
deriving DecidableEq

def auxSource (f : RFlags) : AuxSource :=
  if f.planarFresh && f.planarDepthValid then .planar else .env

-- IBL source priority (shader.c fallback): fresh dynamic cubemap wins,
-- else the dummy white cubemap (anti-NaN last resort).
inductive Source where
  | dynamic
  | dummy
deriving DecidableEq

def iblSource (f : RFlags) : Source :=
  if f.cubeFresh then .dynamic else .dummy

-- Reset clears every flag.
theorem reset_clears_all :
    reset = { planarFresh := false, cubeFresh := false, ssrDrew := false, planarDepthValid := false } := rfl

-- Rendering sets its own flag.
theorem render_planar_sets (f : RFlags) :
    (renderPlanar f).planarFresh = true ∧ (renderPlanar f).planarDepthValid = true := by
  simp [renderPlanar]

theorem render_cube_sets (f : RFlags) : (renderCube f).cubeFresh = true := rfl

theorem render_ssr_sets (f : RFlags) : (renderSSR f).ssrDrew = true := rfl

-- A skipped frame after reset stays fully cleared (no stale-fresh).
theorem skip_keeps_cleared : skip reset = reset := rfl

-- Consumers imply freshness: planar aux bind ⇒ planar was rendered.
theorem planar_consume_gated (f : RFlags) (h : planarOk f = true) :
    f.planarFresh = true := h

--ai: abstract ghost premise only; a C planar bind does not imply this per-pixel fact.
theorem planar_consume_depth (f : RFlags) (h : planarDepthOk f = true) :
    f.planarDepthValid = true := h

-- Cube consumers (SSR env, IBL fallback) imply the faces rendered.
theorem cube_consume_gated (f : RFlags) (h : cubeOk f = true) :
    f.cubeFresh = true := h

--ai: simplified fallback policy; production also checks IBL readiness and texture IDs.
theorem stale_falls_back (f : RFlags) (h : f.cubeFresh = false) :
    iblSource f = .dummy := by
  simp [iblSource, h]

-- Empty mirror depth ⇒ env fallback (never clear-color veil/tiles).
theorem empty_falls_to_env (f : RFlags) (h : f.planarDepthValid = false) :
    auxSource f = .env := by
  simp [auxSource, h]

--ai: historical name; this theorem proves a Boolean policy, NOT a numerical clear/depth threshold.
theorem depth_cleared_far (f : RFlags) (h : f.planarDepthValid = false) :
    auxSource { f with planarFresh := true } = .env := by
  simp [auxSource, h]

-- Sampler bind targets (v0.6.23 audit: model.c maps loop bound every
-- map as 2D, including maps[CUBEMAP] holding the dynamic env cube —
-- GL_INVALID_OPERATION, sampler reads black, reflections toggle a
-- no-op; shader.c point-shadow/CSM arrays had the same 2D-bind defect).
-- Required GL target per material map slot (raylib order).
inductive TexTarget where
  | tex2D
  | cube
  | array2D
deriving DecidableEq

def requiredTarget : Nat → TexTarget
  | 7 => .cube
  | 8 => .cube
  | 9 => .cube
  | _ => .tex2D

theorem cube_slot_needs_cube : requiredTarget 7 = .cube := rfl

theorem irr_slot_needs_cube : requiredTarget 8 = .cube := rfl

theorem pre_slot_needs_cube : requiredTarget 9 = .cube := rfl

theorem albedo_slot_needs_2d : requiredTarget 0 = .tex2D := rfl

-- A bind is legal iff the bind target matches the texture's target.
def bindLegal (texTarget bindAs : TexTarget) : Bool :=
  texTarget == bindAs

theorem mismatch_is_illegal : bindLegal .cube .tex2D = false := rfl

theorem match_is_legal : bindLegal .cube .cube = true := rfl

--ai: illustrative total policy only; failed GL binds can retain previous binding.
-- No theorem here asserts that an illegal sampler operation returns black/zero.
def envTerm (legal : Bool) (bias sample : Nat) : Nat :=
  if legal then bias * sample else 0

theorem illegal_adds_zero (bias sample : Nat) :
    envTerm false bias sample = 0 := rfl

theorem legal_passes (bias sample : Nat) :
    envTerm true bias sample = bias * sample := rfl

-- Unit parking (v0.6.25 validation fix): program validation fails
-- when two ACTIVE samplers of different types share one unit, and
-- strict drivers skip the draw. Frame 1 left the CSM array sampler
-- at default unit 0 (deferred init) next to albedoMap (2D vs ARRAY).
-- The fix parks it on dedicated unit 10 unconditionally.
inductive Sampler where
  | albedo
  | normal
  | cube
  | csm
  | shadow
deriving DecidableEq

def stype : Sampler → TexTarget
  | .albedo | .normal => .tex2D
  | .cube => .cube
  | .csm => .array2D
  | .shadow => .tex2D

--ai: selected initial sampler parking, not the complete runtime per-draw texture map.
def unitOf (parked : Bool) : Sampler → Nat
  | .albedo => 0
  | .normal => 0
  | .cube => 9
  | .csm => if parked then 10 else 0
  | .shadow => 8

def collides (u : Sampler → Nat) (a b : Sampler) : Bool :=
  u a == u b && decide (stype a ≠ stype b)

-- Regression pin: unparked CSM collides with albedo on unit 0.
theorem unparked_csm_collides_albedo :
    collides (unitOf false) .csm .albedo = true := rfl

-- Parked CSM shares a unit with nothing of a different type.
theorem parked_csm_clean_albedo :
    collides (unitOf true) .csm .albedo = false := rfl

theorem parked_csm_clean_normal :
    collides (unitOf true) .csm .normal = false := rfl

theorem parked_csm_clean_cube :
    collides (unitOf true) .csm .cube = false := rfl

theorem parked_csm_clean_shadow :
    collides (unitOf true) .csm .shadow = false := rfl

-- Same-type unit sharing stays legal (seven 2D samplers share unit 0).
theorem shared_2d_unit_ok :
    collides (unitOf true) .albedo .normal = false := rfl

--ai: actual fallback branch in shader.c, including precomputed IBL and resource existence.
inductive IblBranch where
  | precomputed | dynamic | dummy | unchanged
deriving DecidableEq

def productionIblBranch (ready dynamicExists cubeFresh dummyExists : Bool) : IblBranch :=
  if ready then .precomputed
  else if dynamicExists && cubeFresh then .dynamic
  else if dummyExists then .dummy else .unchanged

theorem dynamic_requires_resource_and_freshness (ready resource fresh dummy : Bool)
    (h : productionIblBranch ready resource fresh dummy = .dynamic) :
    ready = false ∧ resource = true ∧ fresh = true := by
  cases ready <;> cases resource <;> cases fresh <;> cases dummy <;>
    simp_all [productionIblBranch]

theorem stale_with_dummy (resource : Bool) :
    productionIblBranch false resource false true = .dummy := by
  simp [productionIblBranch]

theorem absent_fallback_keeps_bindings : productionIblBranch false false false false = .unchanged := rfl

--ai: C binding gate in Draw_SSR; mask existence/occupancy is NOT required by this gate.
def productionPlanarBind (overrideEnabled auxEnabled filled mapLocationAvailable : Bool) : Bool :=
  overrideEnabled && auxEnabled && filled && mapLocationAvailable

theorem planar_bind_requires_freshness (a b f l : Bool)
    (h : productionPlanarBind a b f l = true) : f = true := by
  cases a <;> cases b <;> cases f <;> cases l <;> simp_all [productionPlanarBind]

--ai: shader mask subgate; other UV/edge/water/march/grazing conditions remain separate.
def productionDepthGate (maskAvailable belowThreshold : Bool) : Bool :=
  !maskAvailable || belowThreshold

theorem absent_mask_allows_legacy_sampling (below : Bool) : productionDepthGate false below = true := rfl

theorem available_empty_mask_rejects : productionDepthGate true false = false := rfl

theorem available_mask_requires_valid_sample (below : Bool)
    (h : productionDepthGate true below = true) : below = true := by
  simpa [productionDepthGate] using h

theorem missing_mask_counterexample :
    productionPlanarBind true true true true = true ∧ productionDepthGate false false = true := by decide

theorem sky_sampler_parking_matches_constant : unitOf true .cube = 9 := rfl

end GxProofs.ReflectFlags
