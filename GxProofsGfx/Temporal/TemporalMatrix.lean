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
  //ai: camera VP correspondence over exact rationals, not IEEE or GL verification.
  Numeric-field matrix R has rows m0..m3; physical gX_Matrix rows are
  m0,m4,m8,m12. Thus &matrix.m0 represents transpose R in row-major memory.
  GL_TRUE uploads transpose R to GLSL, implementing row-vector action by R.
  Grounded in common/types/matrix.h, gxmath/matrix.c, wrappers/shader.c,
  gfx/taa.c and gfx/gfx_pipeline.c. Inverse correctness is a hypothesis;
  singular/ill-conditioned C inversion and previous-frame snapshot timing are
  not established by these ideal contracts.
-/
import GxMath.ClipMatrix
import GxProofsGfx.Temporal.TemporalSampling

namespace GxProofsGfx.TemporalMatrix
open GxMath.ClipMatrix

def physicalRows (r : Mat4) : Mat4 := transpose r
def upload (transposeFlag : Bool) (r : Mat4) : Mat4 :=
  if transposeFlag then physicalRows r else transpose (physicalRows r)

theorem transpose_twice (r : Mat4) : transpose (transpose r) = r := by
  ext <;> rfl

theorem raw_true_upload (r : Mat4) : upload true r = transpose r := rfl

theorem raw_false_upload (r : Mat4) : upload false r = r := transpose_twice r

theorem raw_upload_row_action (r : Mat4) (v : Vec4) :
    colMul (upload true r) v = rowMul v r := by
  ext <;> simp [upload, physicalRows, transpose, colMul, rowMul] <;> ring

theorem shader_view_then_projection (view projection : Mat4) (world : Vec4) :
    colMul (upload true (matMul view projection)) world =
      rowMul (rowMul world view) projection := by
  rw [raw_upload_row_action, rowMul_matMul]

def scale (v : Vec4) (k : ℚ) : Vec4 := ⟨v.x*k, v.y*k, v.z*k, v.w*k⟩
def normalize (v : Vec4) : Vec4 := scale v (1/v.w)

theorem row_action_scale (v : Vec4) (m : Mat4) (k : ℚ) :
    rowMul (scale v k) m = scale (rowMul v m) k := by
  ext <;> simp [scale, rowMul] <;> ring

theorem normalize_scale (v : Vec4) (k : ℚ) (hw : v.w ≠ 0) (hk : k ≠ 0) :
    normalize (scale v k) = normalize v := by
  ext <;> simp [normalize, scale] <;> field_simp <;> ring

theorem normalized_unit_world (v : Vec4) (hw : v.w = 1) : normalize v = v := by
  ext <;> simp [normalize, scale, hw]

theorem inverse_row_roundtrip (current inverse : Mat4) (world : Vec4)
    (hi : matMul current inverse = matId) :
    rowMul (rowMul world current) inverse = world := by
  rw [← rowMul_matMul, hi]
  ext <;> simp [rowMul, matId]

theorem inverse_homogeneous_w (current inverse : Mat4) (world : Vec4)
    (hi : matMul current inverse = matId) (hw : world.w = 1) :
    (colMul (upload true inverse) (normalize (rowMul world current))).w =
      1 / (rowMul world current).w := by
  rw [raw_upload_row_action]
  unfold normalize
  rw [row_action_scale, inverse_row_roundtrip current inverse world hi]
  simp [scale, hw]

--ai: clip has been de-jittered before this shader-equivalent inverse action.
theorem ideal_world_reconstruction (current inverse : Mat4) (world : Vec4)
    (hi : matMul current inverse = matId) (hw : world.w = 1)
    (hc : (rowMul world current).w ≠ 0) :
    normalize (colMul (upload true inverse) (normalize (rowMul world current))) = world := by
  rw [raw_upload_row_action]
  unfold normalize
  rw [row_action_scale, inverse_row_roundtrip current inverse world hi]
  change normalize (scale world (1/(rowMul world current).w)) = world
  rw [normalize_scale world _ (by simp [hw]) (one_div_ne_zero hc), normalized_unit_world world hw]

theorem ideal_previous_clip (current inverse previous : Mat4) (world : Vec4)
    (hi : matMul current inverse = matId) (hw : world.w = 1)
    (hc : (rowMul world current).w ≠ 0) :
    colMul (upload true previous)
      (normalize (colMul (upload true inverse) (normalize (rowMul world current)))) =
      rowMul world previous := by
  rw [ideal_world_reconstruction current inverse world hi hw hc, raw_upload_row_action]

theorem previous_w_guard (current inverse previous : Mat4) (world : Vec4)
    (hi : matMul current inverse = matId) (hw : world.w = 1)
    (hc : (rowMul world current).w ≠ 0) (hp : 1/100000 < (rowMul world previous).w) :
    1/100000 < (colMul (upload true previous)
      (normalize (colMul (upload true inverse) (normalize (rowMul world current))))).w := by
  rw [ideal_previous_clip current inverse previous world hi hw hc]
  exact hp

--ai: connects the matrix path to the scalar fallback's actual previous history location.
theorem ideal_history_x (current inverse previous : Mat4) (world : Vec4)
    (uv prevJitter : ℚ) (hi : matMul current inverse = matId) (hw : world.w = 1)
    (hc : (rowMul world current).w ≠ 0) :
    let clip := colMul (upload true previous)
      (normalize (colMul (upload true inverse) (normalize (rowMul world current))))
    TemporalSampling.historyUV uv
      (TemporalSampling.fallbackVelocity uv (TemporalSampling.project clip.x clip.w) prevJitter) =
      TemporalSampling.project (rowMul world previous).x (rowMul world previous).w + prevJitter / 2 := by
  dsimp only
  rw [ideal_previous_clip current inverse previous world hi hw hc]
  exact TemporalSampling.fallback_samples_previous_jitter _ _ _

--ai: asymmetric witnesses distinguish wrong transpose and wrong multiplication order.
def translated : Mat4 := { matId with m30 := 2 }
def stretched : Mat4 := { matId with m00 := 3 }
def origin : Vec4 := ⟨0,0,0,1⟩

theorem wrong_upload_changes_translation :
    (colMul (upload true translated) origin).x = 2 ∧
    (colMul (upload false translated) origin).x = 0 := by
  norm_num [upload, physicalRows, transpose, translated, matId, colMul, origin]

theorem wrong_order_changes_composition :
    (rowMul origin (matMul translated stretched)).x = 6 ∧
    (rowMul origin (matMul stretched translated)).x = 2 := by
  norm_num [rowMul, origin, matMul, translated, stretched, matId]

end GxProofsGfx.TemporalMatrix
