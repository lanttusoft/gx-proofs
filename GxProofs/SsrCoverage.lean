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
  //ai: Boolean correspondence for the existing optional SSR mirror-view routes.
  Inputs below abbreviate comparisons already evaluated by gfx_ssr.frag; proofs
  do not establish floating-point comparisons, GPU completion or visibility.
  optionalFallback is a DESIGN contract, not the production priority order.
-/
import GxProofs.ReflectFlags

namespace GxProofs.SsrCoverage

def auxMiss (available water geometryHit crossed grazed rejected : Bool) : Bool :=
  available && !water && !geometryHit && (crossed || grazed || rejected)

def auxWrongSide (available water geometryHit wrongSide : Bool) : Bool :=
  available && !water && geometryHit && wrongSide

def auxSeam (available water geometryHit onPlane lowMargin : Bool) : Bool :=
  available && !water && geometryHit && onPlane && lowMargin

def auxRoute (available water geometryHit crossed grazed rejected
    wrongSide onPlane lowMargin : Bool) : Bool :=
  auxMiss available water geometryHit crossed grazed rejected ||
  auxWrongSide available water geometryHit wrongSide ||
  auxSeam available water geometryHit onPlane lowMargin

theorem disabled_aux_never_routes (w h c g r s p m : Bool) :
    auxRoute false w h c g r s p m = false := by
  simp [auxRoute, auxMiss, auxWrongSide, auxSeam]

theorem water_never_routes_to_mirror (a h c g r s p m : Bool) :
    auxRoute a true h c g r s p m = false := by
  simp [auxRoute, auxMiss, auxWrongSide, auxSeam]

theorem clean_miss_preserves_environment (a w s p m : Bool) :
    auxRoute a w false false false false s p m = false := by
  simp [auxRoute, auxMiss, auxWrongSide, auxSeam]

theorem accepted_hit_not_a_miss (a w c g r : Bool) :
    auxMiss a w true c g r = false := by simp [auxMiss]

theorem front_side_interior_hit_keeps_march (a w c g r p : Bool) :
    auxRoute a w true c g r false p false = false := by
  simp [auxRoute, auxMiss, auxWrongSide, auxSeam]

--ai: a graze can route even with zero crossings; do not conflate cleanEscape with this gate.
theorem zero_crossings_does_not_mean_no_aux :
    auxRoute true false false false true false false false false = true := rfl

def productionSampleGate (maskAvailable depthOccupied edgeUsable : Bool) : Bool :=
  ReflectFlags.productionDepthGate maskAvailable depthOccupied && edgeUsable

theorem present_empty_depth_rejects (edge : Bool) :
    productionSampleGate true false edge = false := by
  simp [productionSampleGate, ReflectFlags.productionDepthGate]

theorem no_mask_can_accept_unoccupied_sample :
    productionSampleGate false false true = true := rfl

theorem stale_mirror_cannot_bind (overrideEnabled auxEnabled location : Bool) :
    ReflectFlags.productionPlanarBind overrideEnabled auxEnabled false location = false := by
  simp [ReflectFlags.productionPlanarBind]

--ai: usableProbe abbreviates readiness/count and a selected baked, nonzero cube.
-- Actual nearest-distance selection, sky-LUT readiness and sampled radiance are not proved.
inductive EnvironmentSource where
  | dynamic | probe | sky
  deriving DecidableEq

def productionEnvironment (dynamicFresh dynamicExists usableProbe : Bool) : EnvironmentSource :=
  if usableProbe then .probe
  else if dynamicFresh && dynamicExists then .dynamic
  else .sky

theorem usable_probe_overrides_dynamic (fresh resource : Bool) :
    productionEnvironment fresh resource true = .probe := rfl

theorem stale_dynamic_without_probe_uses_sky (resource : Bool) :
    productionEnvironment false resource false = .sky := by simp [productionEnvironment]

theorem missing_dynamic_without_probe_uses_sky (fresh : Bool) :
    productionEnvironment fresh false false = .sky := by simp [productionEnvironment]

theorem dynamic_source_requires_fresh_resource (f r p : Bool)
    (h : productionEnvironment f r p = .dynamic) :
    f = true ∧ r = true ∧ p = false := by
  cases f <;> cases r <;> cases p <;> simp_all [productionEnvironment]

--ai: proposed optional-camera eligibility. A frame-level filled flag is insufficient.
structure CameraEvidence where
  fresh : Bool
  colorAvailable : Bool
  depthAvailable : Bool
  projectedInside : Bool
  positiveW : Bool
  rayHitValidated : Bool
  deriving DecidableEq

def cameraUsable (e : CameraEvidence) : Bool :=
  e.fresh && e.colorAvailable && e.depthAvailable && e.projectedInside &&
    e.positiveW && e.rayHitValidated

theorem camera_requires_all_evidence (e : CameraEvidence) (h : cameraUsable e = true) :
    e.fresh = true ∧ e.colorAvailable = true ∧ e.depthAvailable = true ∧
      e.projectedInside = true ∧ e.positiveW = true ∧ e.rayHitValidated = true := by
  simpa [cameraUsable, Bool.and_eq_true, and_assoc] using h

theorem missing_depth_camera_unusable (f c i w r : Bool) :
    cameraUsable ⟨f,c,false,i,w,r⟩ = false := by simp [cameraUsable]

theorem unvalidated_camera_unusable (f c d i w : Bool) :
    cameraUsable ⟨f,c,d,i,w,false⟩ = false := by simp [cameraUsable]

inductive Source where
  | screen | analytic | cubemap | camera | omit
  deriving DecidableEq

def optionalFallback (screenValid analyticValid cubemapValid cameraEnabled : Bool)
    (camera : CameraEvidence) : Source :=
  if screenValid then .screen
  else if analyticValid then .analytic
  else if cubemapValid then .cubemap
  else if cameraEnabled && cameraUsable camera then .camera
  else .omit

theorem valid_screen_wins (a c enabled : Bool) (e : CameraEvidence) :
    optionalFallback true a c enabled e = .screen := rfl

theorem valid_analytic_wins (c enabled : Bool) (e : CameraEvidence) :
    optionalFallback false true c enabled e = .analytic := rfl

theorem valid_cubemap_wins (enabled : Bool) (e : CameraEvidence) :
    optionalFallback false false true enabled e = .cubemap := rfl

theorem camera_is_only_last_resort (s a c enabled : Bool) (e : CameraEvidence)
    (h : optionalFallback s a c enabled e = .camera) :
    s = false ∧ a = false ∧ c = false ∧ enabled = true ∧ cameraUsable e = true := by
  cases s <;> cases a <;> cases c <;> cases enabled <;>
    simp_all [optionalFallback]

theorem optional_camera_off_omits_gap (e : CameraEvidence) :
    optionalFallback false false false false e = .omit := rfl

theorem invalid_camera_omits_gap (enabled : Bool) (e : CameraEvidence)
    (h : cameraUsable e = false) :
    optionalFallback false false false enabled e = .omit := by
  simp [optionalFallback, h]

end GxProofs.SsrCoverage
