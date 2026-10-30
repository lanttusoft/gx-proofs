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
  //ai: exact homogeneous winding and canonical near-plane clipping before perspective divide.
  Full GPU frustum clipping, raster precision and IEEE projection remain external.
-/
import GxProofsGfx.Ssr.ReflectionHandedness

namespace GxProofsGfx.ProjectionClipping
open GxMath.ClipMatrix ReflectionHandedness

def determinantXYW (a b c : Vec4) : ℚ :=
  a.x*(b.y*c.w-b.w*c.y)-a.y*(b.x*c.w-b.w*c.x)+a.w*(b.x*c.y-b.y*c.x)

def projectedArea (a b c : Vec4) : ℚ := area (a.x/a.w) (a.y/a.w) (b.x/b.w) (b.y/b.w) (c.x/c.w) (c.y/c.w)

theorem perspective_area_identity (a b c : Vec4) (ha : a.w ≠ 0) (hb : b.w ≠ 0) (hc : c.w ≠ 0) :
    projectedArea a b c = determinantXYW a b c / (a.w*b.w*c.w) := by
  unfold projectedArea area determinantXYW
  field_simp
  ring

theorem positive_w_orientation (a b c : Vec4) (ha : 0 < a.w) (hb : 0 < b.w) (hc : 0 < c.w) :
    (0 < projectedArea a b c ↔ 0 < determinantXYW a b c) := by
  rw [perspective_area_identity a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)]
  exact div_pos_iff_of_pos_right (mul_pos (mul_pos ha hb) hc)

theorem uv_area_preserves_sign_scale (a b c : Vec4) :
    area (PlanarReflection.projectedU a) (PlanarReflection.projectedV a)
      (PlanarReflection.projectedU b) (PlanarReflection.projectedV b)
      (PlanarReflection.projectedU c) (PlanarReflection.projectedV c) = projectedArea a b c / 4 := by
  unfold PlanarReflection.projectedU PlanarReflection.projectedV projectedArea area
  ring

def lerp (a b : Vec4) (t : ℚ) : Vec4 :=
  ⟨(1-t)*a.x+t*b.x,(1-t)*a.y+t*b.y,(1-t)*a.z+t*b.z,(1-t)*a.w+t*b.w⟩

def nearDistance (p : Vec4) : ℚ := p.z+p.w

theorem near_distance_linear (a b : Vec4) (t : ℚ) :
    nearDistance (lerp a b t) = (1-t)*nearDistance a+t*nearDistance b := by
  simp [nearDistance, lerp]
  ring

--ai: canonical near half-space z+w >= 0, not an invented w epsilon GPU plane.
def nearIntersection (a b : Vec4) : ℚ := -nearDistance a/(nearDistance b-nearDistance a)

theorem near_intersection_boundary (a b : Vec4) (ha : nearDistance a < 0) (hb : 0 ≤ nearDistance b) :
    nearDistance (lerp a b (nearIntersection a b)) = 0 := by
  have hd : nearDistance b-nearDistance a ≠ 0 := by linarith
  rw [near_distance_linear]
  unfold nearIntersection
  field_simp
  ring

theorem near_intersection_parameter (a b : Vec4) (ha : nearDistance a < 0) (hb : 0 < nearDistance b) :
    0 < nearIntersection a b ∧ nearIntersection a b < 1 := by
  have hd : 0 < nearDistance b-nearDistance a := by linarith
  unfold nearIntersection
  constructor
  · exact div_pos (by linarith) hd
  · rw [div_lt_one hd]
    linarith

def perspectiveZ (w near far : ℚ) : ℚ := (far+near)/(far-near)*w-2*far*near/(far-near)

theorem perspective_near_distance (w near far : ℚ) (h : far-near ≠ 0) :
    perspectiveZ w near far+w = (2*far/(far-near))*(w-near) := by
  unfold perspectiveZ
  field_simp
  ring

theorem standard_near_clip_implies_positive_w (w near far : ℚ)
    (hn : 0 < near) (hf : near < far) (hclip : 0 ≤ perspectiveZ w near far+w) :
    near ≤ w ∧ 0 < w := by
  have hd : 0 < far-near := by linarith
  rw [perspective_near_distance w near far (ne_of_gt hd)] at hclip
  have factor : 0 < 2*far/(far-near) := div_pos (by linarith) hd
  have hw : near ≤ w := by nlinarith
  exact ⟨hw,lt_of_lt_of_le hn hw⟩

theorem perspective_z_affine (a b t near far : ℚ) :
    perspectiveZ ((1-t)*a+t*b) near far =
      (1-t)*perspectiveZ a near far+t*perspectiveZ b near far := by
  unfold perspectiveZ
  ring

theorem near_intersection_positive_w (a b : Vec4) (near far : ℚ)
    (hn : 0 < near) (hf : near < far) (ha : nearDistance a < 0) (hb : 0 ≤ nearDistance b)
    (haz : a.z = perspectiveZ a.w near far) (hbz : b.z = perspectiveZ b.w near far) :
    near ≤ (lerp a b (nearIntersection a b)).w ∧ 0 < (lerp a b (nearIntersection a b)).w := by
  have consistent : (lerp a b (nearIntersection a b)).z =
      perspectiveZ (lerp a b (nearIntersection a b)).w near far := by
    simp only [lerp, haz, hbz]
    rw [perspective_z_affine]
  have boundary := near_intersection_boundary a b ha hb
  unfold nearDistance at boundary
  rw [consistent] at boundary
  exact standard_near_clip_implies_positive_w _ near far hn hf (le_of_eq boundary.symm)

--ai: rounding/perturbation allowance is supplied; positivity requires this lower bound itself to be positive.
theorem affine_near_clip_error_margin (w scale bias error uncertainty : ℚ)
    (hs : 0 < scale) (he : error ≤ uncertainty) (hc : 0 ≤ scale*w-bias+error) :
    (bias-uncertainty)/scale ≤ w := by
  rw [div_le_iff₀ hs]
  nlinarith

--ai: one-outside-vertex near clip produces an oriented quad; these are its two fan triangles.
theorem clipped_fan_first (a b c : Vec4) (s : ℚ) :
    determinantXYW (lerp a b s) b c = (1-s)*determinantXYW a b c := by
  simp [determinantXYW, lerp]
  ring

theorem clipped_fan_second (a b c : Vec4) (s t : ℚ) :
    determinantXYW (lerp a b s) c (lerp a c t) = s*(1-t)*determinantXYW a b c := by
  simp [determinantXYW, lerp]
  ring

theorem clipped_fan_positive_orientation (a b c : Vec4) (s t : ℚ)
    (hs : 0 < s) (hs1 : s < 1) (ht1 : t < 1) (hd : 0 < determinantXYW a b c) :
    0 < determinantXYW (lerp a b s) b c ∧ 0 < determinantXYW (lerp a b s) c (lerp a c t) := by
  rw [clipped_fan_first, clipped_fan_second]
  exact ⟨mul_pos (by linarith) hd,mul_pos (mul_pos hs (by linarith)) hd⟩

theorem crossing_camera_plane_counterexample :
    0 < determinantXYW ⟨-1,-1,0,-1⟩ ⟨1,-1,0,1⟩ ⟨0,1,0,1⟩ ∧
    projectedArea ⟨-1,-1,0,-1⟩ ⟨1,-1,0,1⟩ ⟨0,1,0,1⟩ < 0 := by
  norm_num [determinantXYW, projectedArea, area]

end GxProofsGfx.ProjectionClipping
