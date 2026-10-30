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
  //ai: source-grounded glass routing witnesses and conditional capture/feedback algebra.
  gfx_render.c and draw.c route blending only below 0.999; model.c binds bgTex
  for any enabled refraction; the background copy runs after the opaque draw.
  The historical routing counterexample is retained. Native repair routes active
  refraction through needsPostCapture and gates sampling on phase-local readiness.
  This is NOT an unconditional proof that the engine or GPU transfer is correct.
  Rational opacity idealizes finite floats; alpha=1 is an exact executable witness.
  GPU capture identity, GL binding/order, camera stamps, filtering and numerical
  accuracy remain obligations for native/GPU tests. No temporal filter is modeled.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace GxProofsGfx.GlassCapture

def currentTransparent (blending : Bool) (opacity : ℚ) : Prop :=
  blending = true ∧ opacity < 999 / 1000

theorem opacity_one_not_transparent (blending : Bool) :
    ¬ currentTransparent blending 1 := by
  intro h
  have hlt := h.2
  norm_num at hlt

theorem below_threshold_transparent (opacity : ℚ) (h : opacity < 999 / 1000) :
    currentTransparent true opacity := by
  exact ⟨rfl, h⟩

--ai: Refraction here means effective QUALITY>=1 refraction; native tests check that feature gate.
def needsPostCapture (refractive blending : Bool) (opacity : ℚ) : Prop :=
  refractive = true ∨ currentTransparent blending opacity

theorem refractive_opacity_one_requires_post_capture (blending : Bool) :
    needsPostCapture true blending 1 := by
  exact Or.inl rfl

theorem active_refraction_requires_post_capture (blending : Bool) (opacity : ℚ) :
    needsPostCapture true blending opacity := by
  exact Or.inl rfl

theorem nonrefractive_route_preserved (blending : Bool) (opacity : ℚ) :
    needsPostCapture false blending opacity ↔ currentTransparent blending opacity := by
  simp [needsPostCapture]

theorem current_route_does_not_imply_capture_safety :
    needsPostCapture true true 1 ∧ ¬ currentTransparent true 1 := by
  exact ⟨refractive_opacity_one_requires_post_capture true,
    opacity_one_not_transparent true⟩

structure CaptureStamp where
  frame : ℕ
  camera : ℕ
  width : ℕ
  height : ℕ
  deriving DecidableEq

--ai: labels encode validity premises; native code must establish, not assume, them.
def safeRead (source destination : ℕ) (capture draw : CaptureStamp) : Prop :=
  source ≠ destination ∧ capture = draw

theorem safe_read_distinct_targets (source destination : ℕ) (capture draw : CaptureStamp)
    (h : safeRead source destination capture draw) : source ≠ destination := h.1

theorem safe_read_current_frame (source destination : ℕ) (capture draw : CaptureStamp)
    (h : safeRead source destination capture draw) : capture.frame = draw.frame := by
  rw [h.2]

theorem safe_read_current_camera (source destination : ℕ) (capture draw : CaptureStamp)
    (h : safeRead source destination capture draw) : capture.camera = draw.camera := by
  rw [h.2]

theorem prior_frame_not_safe (source destination : ℕ) (capture draw : CaptureStamp)
    (hprior : capture.frame + 1 = draw.frame) :
    ¬ safeRead source destination capture draw := by
  intro h
  have hsame := safe_read_current_frame source destination capture draw h
  omega

--ai: conditional ideal recurrence if an old rendered pixel feeds the next draw.
def feedback (alpha background previous : ℚ) : ℚ :=
  (1 - alpha) * background + alpha * previous

theorem full_opacity_retains_previous (background previous : ℚ) :
    feedback 1 background previous = previous := by
  simp [feedback]

theorem feedback_memory_difference (alpha background first second : ℚ) :
    feedback alpha background first - feedback alpha background second =
      alpha * (first - second) := by
  unfold feedback
  ring

theorem zero_opacity_removes_feedback (background previous : ℚ) :
    feedback 0 background previous = background := by
  simp [feedback]

--ai: historical background copy blended using HDR roughness alpha as if it were coverage.
def blendedCopy (roughness source previous : ℚ) : ℚ :=
  roughness * source + (1 - roughness) * previous

theorem blended_copy_retains_history (roughness source first second : ℚ) :
    blendedCopy roughness source first - blendedCopy roughness source second =
      (1 - roughness) * (first - second) := by
  unfold blendedCopy
  ring

theorem half_roughness_copy_not_overwrite : blendedCopy (1/2) 1 0 ≠ 1 := by
  norm_num [blendedCopy]

--ai: framebuffer transfer identity is a GPU premise, not certified by this abstract operation.
def overwriteCopy (source _previous : ℚ) : ℚ := source

theorem overwrite_copy_independent_of_history (source first second : ℚ) :
    overwriteCopy source first = overwriteCopy source second := by
  rfl

end GxProofsGfx.GlassCapture
