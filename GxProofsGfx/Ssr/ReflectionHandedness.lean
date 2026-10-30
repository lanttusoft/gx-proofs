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
  //ai: exact reflected-frame orientation and conditional projected winding.
  Normalization factors/unit-frame hypotheses are supplied, not IEEE sqrt proofs.
  3D orientation reversal alone does not determine GPU projected-face culling.
-/
import GxProofsGfx.Ssr.PlanarReflection

namespace GxProofsGfx.ReflectionHandedness
open GxMath.ClipMatrix PlanarReflection

def cross (a b : Vec4) : Vec4 :=
  ⟨a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x,0⟩
def neg (v : Vec4) : Vec4 := ⟨-v.x,-v.y,-v.z,-v.w⟩
def orientation (x y z : Vec4) : ℚ := dot (cross x y) z

def difference (a b : Vec4) : Vec4 := ⟨a.x-b.x,a.y-b.y,a.z-b.z,a.w-b.w⟩

--ai: reflected position-target delta has no offset translation, as required by LookAt's back axis.
theorem camera_delta_reflects_as_direction (n a b : Vec4) (d : ℚ) (hw : a.w = b.w) :
    difference (reflect n d a) (reflect n d b) = reflect n 0 (difference a b) := by
  ext <;> simp [difference, reflect, signed, dot, hw] <;> ring

theorem cross_dot_zero (a b : Vec4) : dot (cross a b) b = 0 := by
  simp [cross, dot]
  ring

theorem dot_reflection_preserved (n a b : Vec4) (hn : dot n n = 1) :
    dot (reflect n 0 a) (reflect n 0 b) = dot a b := by
  simp only [reflect, signed, dot] at *
  linear_combination 4*(n.x*a.x+n.y*a.y+n.z*a.z)*(n.x*b.x+n.y*b.y+n.z*b.z)*hn

theorem cross_reflection_reversed (n a b : Vec4) (hn : dot n n = 1) :
    cross (reflect n 0 a) (reflect n 0 b) = neg (reflect n 0 (cross a b)) := by
  ext
  · simp only [cross, reflect, signed, dot, neg] at *
    linear_combination -2*(a.y*b.z-a.z*b.y)*hn
  · simp only [cross, reflect, signed, dot, neg] at *
    linear_combination -2*(a.z*b.x-a.x*b.z)*hn
  · simp only [cross, reflect, signed, dot, neg] at *
    linear_combination -2*(a.x*b.y-a.y*b.x)*hn
  · simp [cross, neg, reflect]

theorem dot_neg_left (a b : Vec4) : dot (neg a) b = -dot a b := by
  simp [dot, neg]
  ring

theorem reflection_reverses_orientation (n x y z : Vec4) (hn : dot n n = 1) :
    orientation (reflect n 0 x) (reflect n 0 y) (reflect n 0 z) = -orientation x y z := by
  unfold orientation
  rw [cross_reflection_reversed n x y hn, dot_neg_left, dot_reflection_preserved n (cross x y) z hn]

--ai: same exact normalization factors are justified by isometry, not inferred from C sqrt rounding.
def lookX (up z : Vec4) (k : ℚ) : Vec4 := TemporalMatrix.scale (cross up z) k
def lookY (z x : Vec4) : Vec4 := cross z x

theorem look_x_perpendicular_z (up z : Vec4) (k : ℚ) : dot (lookX up z k) z = 0 := by
  simp [lookX, TemporalMatrix.scale, dot, cross]
  ring

theorem look_frame_orientation_identity (x z : Vec4) :
    orientation x (lookY z x) z = dot x x * dot z z - (dot x z)^2 := by
  simp [orientation, lookY, dot, cross]
  ring

theorem normalized_look_frame_right_handed (up z : Vec4) (k : ℚ)
    (hx : dot (lookX up z k) (lookX up z k) = 1) (hz : dot z z = 1) :
    orientation (lookX up z k) (lookY z (lookX up z k)) z = 1 := by
  rw [look_frame_orientation_identity, hx, hz, look_x_perpendicular_z]
  norm_num

theorem reflect_scale (n v : Vec4) (k : ℚ) :
    reflect n 0 (TemporalMatrix.scale v k) = TemporalMatrix.scale (reflect n 0 v) k := by
  ext <;> simp [reflect, signed, dot, TemporalMatrix.scale] <;> ring

theorem scale_neg (v : Vec4) (k : ℚ) :
    TemporalMatrix.scale (neg v) k = neg (TemporalMatrix.scale v k) := by
  ext <;> simp [TemporalMatrix.scale, neg] <;> ring

theorem mirrored_look_right_axis (n up z : Vec4) (k : ℚ) (hn : dot n n = 1) :
    lookX (reflect n 0 up) (reflect n 0 z) k = neg (reflect n 0 (lookX up z k)) := by
  unfold lookX
  rw [cross_reflection_reversed n up z hn, scale_neg, reflect_scale]

theorem cross_neg_right (a b : Vec4) : cross a (neg b) = neg (cross a b) := by
  ext <;> simp [cross, neg] <;> ring

theorem neg_neg (v : Vec4) : neg (neg v) = v := by
  ext <;> simp [neg]

theorem mirrored_look_up_axis (n up z : Vec4) (k : ℚ) (hn : dot n n = 1) :
    lookY (reflect n 0 z) (lookX (reflect n 0 up) (reflect n 0 z) k) =
      reflect n 0 (lookY z (lookX up z k)) := by
  rw [mirrored_look_right_axis n up z k hn]
  unfold lookY
  rw [cross_neg_right, cross_reflection_reversed n z (lookX up z k) hn, neg_neg]

theorem dot_neg_both (a b : Vec4) : dot (neg a) (neg b) = dot a b := by
  simp [dot, neg]

theorem mirrored_look_rebuilds_right_handed (n up z : Vec4) (k : ℚ)
    (hn : dot n n = 1) (hx : dot (lookX up z k) (lookX up z k) = 1) (hz : dot z z = 1) :
    orientation (lookX (reflect n 0 up) (reflect n 0 z) k)
      (lookY (reflect n 0 z) (lookX (reflect n 0 up) (reflect n 0 z) k)) (reflect n 0 z) = 1 := by
  apply normalized_look_frame_right_handed
  · rw [mirrored_look_right_axis n up z k hn, dot_neg_both, dot_reflection_preserved n _ _ hn, hx]
  · rw [dot_reflection_preserved n z z hn, hz]

--ai: screen-space affine horizontal flip; no assertion that every reflected GPU triangle has this relation.
def area (ax ay bx by_ cx cy : ℚ) : ℚ := (bx-ax)*(cy-ay)-(by_-ay)*(cx-ax)

theorem horizontal_flip_reverses_area (ax ay bx by_ cx cy : ℚ) :
    area (-ax) ay (-bx) by_ (-cx) cy = -area ax ay bx by_ cx cy := by
  unfold area
  ring

def frontFacing (ccw : Bool) (signedArea : ℚ) : Bool :=
  if ccw then decide (0 < signedArea) else decide (signedArea < 0)

theorem winding_switch_compensates_flip (a : ℚ) :
    frontFacing true a = frontFacing false (-a) := by
  simp [frontFacing]

theorem zero_area_not_front : frontFacing true 0 = false ∧ frontFacing false 0 = false := by decide

end GxProofsGfx.ReflectionHandedness
