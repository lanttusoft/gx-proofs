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
  //ai: exact-rational analytic ray/plane intersections and a mirror-camera
  parallax witness. No IEEE error, shader traversal, raster visibility, shading
  or optional general second-camera implementation is certified here.
-/
import GxProofsGfx.Ssr.PlanarReflection

namespace GxProofsGfx.SsrRayCoverage
open GxMath.ClipMatrix PlanarReflection

def pointOnRay (p direction : Vec4) (t : ℚ) : Vec4 :=
  ⟨p.x+t*direction.x,p.y+t*direction.y,p.z+t*direction.z,p.w⟩

def offset (a b : Vec4) : Vec4 := ⟨a.x-b.x,a.y-b.y,a.z-b.z,0⟩

def planeParameter (n p direction : Vec4) (d : ℚ) : ℚ :=
  -signed n d p / dot n direction

theorem signed_on_ray (n p direction : Vec4) (d t : ℚ) :
    signed n d (pointOnRay p direction t) = signed n d p+t*dot n direction := by
  simp [signed, pointOnRay, dot]
  ring

theorem analytic_intersection_on_plane (n p direction : Vec4) (d : ℚ)
    (hden : dot n direction ≠ 0) :
    signed n d (pointOnRay p direction (planeParameter n p direction d)) = 0 := by
  rw [signed_on_ray]
  unfold planeParameter
  field_simp
  ring

theorem analytic_intersection_unique (n p direction : Vec4) (d t : ℚ)
    (hden : dot n direction ≠ 0)
    (hhit : signed n d (pointOnRay p direction t) = 0) :
    t = planeParameter n p direction d := by
  rw [signed_on_ray] at hhit
  unfold planeParameter
  apply (eq_div_iff hden).2
  linarith

theorem parallel_off_plane_has_no_hit (n p direction : Vec4) (d : ℚ)
    (hparallel : dot n direction = 0) (hoff : signed n d p ≠ 0) :
    ∀ t, signed n d (pointOnRay p direction t) ≠ 0 := by
  intro t
  simpa [signed_on_ray, hparallel] using hoff

theorem negative_parameter_is_not_forward_hit (n p direction : Vec4) (d : ℚ)
    (hden : dot n direction ≠ 0) (hbehind : planeParameter n p direction d < 0) :
    ∀ t, 0 ≤ t → signed n d (pointOnRay p direction t) ≠ 0 := by
  intro t hforward hhit
  have heq := analytic_intersection_unique n p direction d t hden hhit
  linarith

--ai: on-plane mirror geometry agrees; actual image occupancy remains unproved.
theorem on_plane_lookup_origin_fixed (n p : Vec4) (d : ℚ)
    (hplane : signed n d p = 0) : reflect n d p = p :=
  on_plane_fixed n p d hplane

--ai: even equal global/local plane normals cannot remove off-plane ray-origin parallax.
def mirrorNormal : Vec4 := ⟨0,1,0,0⟩
def eye : Vec4 := ⟨0,2,0,1⟩
def receiver : Vec4 := ⟨1,1,0,1⟩
def mirrorEye : Vec4 := reflect mirrorNormal 0 eye
def incident : Vec4 := offset receiver eye
def reflectedDirection : Vec4 := reflect mirrorNormal 0 incident
def auxiliaryDirection : Vec4 := offset (reflect mirrorNormal 0 receiver) mirrorEye
def actualHit : Vec4 := pointOnRay receiver reflectedDirection 1

theorem witness_has_unit_plane_normal : dot mirrorNormal mirrorNormal = 1 := by
  norm_num [dot, mirrorNormal]

theorem witness_receiver_off_plane : signed mirrorNormal 0 receiver = 1 := by
  norm_num [signed, dot, mirrorNormal, receiver]

theorem matching_directions_do_not_match_origins :
    reflectedDirection = auxiliaryDirection ∧ receiver ≠ mirrorEye := by
  constructor
  · norm_num [reflectedDirection, auxiliaryDirection, reflect, signed, dot,
      incident, offset, receiver, mirrorEye, mirrorNormal, eye]
  · intro h
    have hx := congrArg Vec4.x h
    norm_num [receiver, mirrorEye, reflect, signed, dot, mirrorNormal, eye] at hx

theorem real_reflection_hits_witness : actualHit = ⟨2,2,0,1⟩ := by
  norm_num [actualHit, pointOnRay, receiver, reflectedDirection, reflect,
    signed, dot, mirrorNormal, incident, offset, eye]

theorem mirror_lookup_ray_misses_actual_hit :
    ∀ t : ℚ, pointOnRay mirrorEye auxiliaryDirection t ≠ actualHit := by
  intro t h
  have hx := congrArg Vec4.x h
  have hy := congrArg Vec4.y h
  norm_num [actualHit, pointOnRay, receiver, reflectedDirection, auxiliaryDirection,
    reflect, signed, dot, mirrorNormal, incident, offset, eye, mirrorEye] at hx hy
  linarith

--ai: clip-w/in-frame gates alone say nothing about ray/depth agreement.
def clipInside (clip : Vec4) : Prop :=
  0 < clip.w ∧ -clip.w ≤ clip.x ∧ clip.x ≤ clip.w ∧
    -clip.w ≤ clip.y ∧ clip.y ≤ clip.w

--ai: conventional GL NDC-to-depth mapping, not reversed-Z or a tolerance model.
def projectedDepth (clip : Vec4) : ℚ := (clip.z/clip.w+1)/2

theorem in_frame_projection_can_disagree_with_stored_depth :
    clipInside ⟨0,0,1/2,1⟩ ∧ projectedU ⟨0,0,1/2,1⟩ = 1/2 ∧
      projectedV ⟨0,0,1/2,1⟩ = 1/2 ∧ projectedDepth ⟨0,0,1/2,1⟩ = 3/4 ∧
      projectedDepth ⟨0,0,1/2,1⟩ ≠ (1/4 : ℚ) := by
  norm_num [clipInside, projectedU, projectedV, projectedDepth]

end GxProofsGfx.SsrRayCoverage
