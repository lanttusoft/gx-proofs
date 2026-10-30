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
  //ai: GL cubemap face coordinates. Nonzero directions, positive major-axis
  scale and strict-interior selection are explicit; hardware seam ties external.
-/
import GxProofsGfx.Ssr.ReflectionHandedness

namespace GxProofsGfx.CubemapGeometry
open GxMath.ClipMatrix

inductive Face where
  | px | nx | py | ny | pz | nz
  deriving DecidableEq

def direction (f : Face) (s t : ℚ) : Vec4 :=
  match f with
  | .px => ⟨1,-t,-s,0⟩
  | .nx => ⟨-1,-t,s,0⟩
  | .py => ⟨s,1,t,0⟩
  | .ny => ⟨s,-1,-t,0⟩
  | .pz => ⟨s,-t,1,0⟩
  | .nz => ⟨-s,-t,-1,0⟩

def sc (f : Face) (d : Vec4) : ℚ :=
  match f with
  | .px => -d.z | .nx => d.z | .py | .ny | .pz => d.x | .nz => -d.x
def tc (f : Face) (d : Vec4) : ℚ :=
  match f with
  | .py => d.z | .ny => -d.z | _ => -d.y
def major (f : Face) (d : Vec4) : ℚ :=
  match f with
  | .px => d.x | .nx => -d.x | .py => d.y | .ny => -d.y | .pz => d.z | .nz => -d.z

theorem face_coordinate_roundtrip (f : Face) (s t : ℚ) :
    sc f (direction f s t) = s ∧ tc f (direction f s t) = t ∧ major f (direction f s t) = 1 := by
  cases f <;> simp [direction,sc,tc,major]

theorem direction_roundtrip (f : Face) (d : Vec4) (hm : major f d ≠ 0) (hw : d.w = 0) :
    TemporalMatrix.scale (direction f (sc f d / major f d) (tc f d / major f d)) (major f d) = d := by
  cases f <;> ext <;> simp_all [direction,sc,tc,major,TemporalMatrix.scale] <;> field_simp

def select (d : Vec4) : Face :=
  if |d.x| ≥ |d.y| ∧ |d.x| ≥ |d.z| then
    if d.x ≥ 0 then .px else .nx
  else if |d.y| ≥ |d.z| then
    if d.y ≥ 0 then .py else .ny
  else if d.z ≥ 0 then .pz else .nz

theorem strict_interior_selection (f : Face) (s t : ℚ)
    (hs : |s| < 1) (ht : |t| < 1) : select (direction f s t) = f := by
  cases f <;> simp [select,direction,abs_neg,le_of_lt hs,le_of_lt ht,not_le_of_gt hs,not_le_of_gt ht]

--ai: shader ties are X then Y then Z; GL seam face choice is not promised here.
theorem positive_corner_tie : select ⟨1,1,1,0⟩ = .px := by
  norm_num [select]

def dot3 (a b : Vec4) : ℚ := a.x*b.x+a.y*b.y+a.z*b.z
def back (f : Face) : Vec4 := TemporalMatrix.scale (direction f 0 0) (-1)
def up (f : Face) : Vec4 :=
  match f with
  | .py => ⟨0,0,1,0⟩ | .ny => ⟨0,0,-1,0⟩ | _ => ⟨0,-1,0,0⟩
def right (f : Face) : Vec4 := ReflectionHandedness.cross (up f) (back f)

theorem capture_axes_match (f : Face) (d : Vec4) :
    dot3 (right f) d = sc f d ∧ dot3 (up f) d = tc f d ∧ dot3 (back f) d = -major f d := by
  cases f <;> simp [dot3,right,up,back,direction,sc,tc,major,ReflectionHandedness.cross,TemporalMatrix.scale]

def uv (s : ℚ) : ℚ := (s+1)/2
theorem uv_bounds (s : ℚ) (hl : -1 ≤ s) (hu : s ≤ 1) : 0 ≤ uv s ∧ uv s ≤ 1 := by
  unfold uv
  constructor <;> linarith

theorem positive_scale_coordinates (f : Face) (d : Vec4) (k : ℚ)
    (hk : 0 < k) (hm : major f d ≠ 0) :
    sc f (TemporalMatrix.scale d k) / major f (TemporalMatrix.scale d k) = sc f d / major f d ∧
    tc f (TemporalMatrix.scale d k) / major f (TemporalMatrix.scale d k) = tc f d / major f d := by
  have hn : k ≠ 0 := ne_of_gt hk
  cases f <;> simp_all [sc,tc,major,TemporalMatrix.scale] <;> constructor <;> field_simp

--ai: adjacent faces represent the same direction on shared edges, not the same UV.
theorem px_nz_edge (t : ℚ) : direction .px 1 t = direction .nz (-1) t := by
  ext <;> simp [direction]
theorem nx_pz_edge (t : ℚ) : direction .nx 1 t = direction .pz (-1) t := by
  ext <;> simp [direction]

theorem negative_x_asymmetry :
    sc .nx ⟨-2,1,1,0⟩ / major .nx ⟨-2,1,1,0⟩ = 1/2 ∧
    - (1 : ℚ) / 2 ≠ sc .nx ⟨-2,1,1,0⟩ / major .nx ⟨-2,1,1,0⟩ := by
  norm_num [sc,major]

end GxProofsGfx.CubemapGeometry
