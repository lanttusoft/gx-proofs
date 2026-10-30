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
  gX — RHI GL State Wrappers Specification

  Models the blend mapping in src/rhi/rhi_state.c:
  gX_RHI_Blend_Mode (gX_RHI_BLEND_* 0..7 = RL_BLEND_* values,
  verified in rhi_enums.h). Enable/Disable, Scissor, Cull_Mode,
  Color_Mask, Depth_Write exist in the same file but are unmodeled
  here — the table below is the full salvage, not the header's
  original aspiration.

  Theorems proven: 13 (blend-mapping table + default-disable)
-/

namespace GxProofs.RhiState

-- GL constant aliases (using standard GL enum values)
def GL_BLEND : Nat := 0x0BE2
def GL_SRC_ALPHA : Nat := 0x0302
def GL_ONE_MINUS_SRC_ALPHA : Nat := 0x0303
def GL_ONE : Nat := 1
def GL_DST_COLOR : Nat := 0x0306
def GL_FUNC_ADD : Nat := 0x8006
def GL_FUNC_SUBTRACT : Nat := 0x800A
def GL_BACK : Nat := 0x0405

-- RL_BLEND_* constants (from rlgl.h)
def RL_BLEND_ALPHA : Nat := 0
def RL_BLEND_ADDITIVE : Nat := 1
def RL_BLEND_MULTIPLIED : Nat := 2
def RL_BLEND_ADD_COLORS : Nat := 3
def RL_BLEND_SUBTRACT_COLORS : Nat := 4
def RL_BLEND_ALPHA_PREMULTIPLY : Nat := 5
def RL_BLEND_CUSTOM : Nat := 6
def RL_BLEND_CUSTOM_SEPARATE : Nat := 7

-- A blend mode describes the combined state
structure BlendState where
  enabled : Bool
  srcRGB : Nat
  dstRGB : Nat
  equation : Nat

def emptyBlend : BlendState :=
  { enabled := false, srcRGB := 0, dstRGB := 0, equation := 0 }

-- Map RL_BLEND_* constant to the corresponding blend state
def blendMode (mode : Nat) : BlendState :=
  match mode with
  | 0 => { enabled := true, srcRGB := GL_SRC_ALPHA, dstRGB := GL_ONE_MINUS_SRC_ALPHA, equation := GL_FUNC_ADD }
  | 1 => { enabled := true, srcRGB := GL_SRC_ALPHA, dstRGB := GL_ONE, equation := GL_FUNC_ADD }
  | 2 => { enabled := true, srcRGB := GL_DST_COLOR, dstRGB := GL_ONE_MINUS_SRC_ALPHA, equation := GL_FUNC_ADD }
  | 3 => { enabled := true, srcRGB := GL_ONE, dstRGB := GL_ONE, equation := GL_FUNC_ADD }
  | 4 => { enabled := true, srcRGB := GL_ONE, dstRGB := GL_ONE, equation := GL_FUNC_SUBTRACT }
  | 5 => { enabled := true, srcRGB := GL_ONE, dstRGB := GL_ONE_MINUS_SRC_ALPHA, equation := GL_FUNC_ADD }
  | 6 => { enabled := true, srcRGB := 0, dstRGB := 0, equation := 0 }
  | 7 => { enabled := true, srcRGB := 0, dstRGB := 0, equation := 0 }
  | _ => { enabled := false, srcRGB := 0, dstRGB := 0, equation := 0 }

-- Overall GL state model
structure State where
  blend : BlendState
  cullFace : Nat
  colorMaskR : Bool
  colorMaskG : Bool
  colorMaskB : Bool
  colorMaskA : Bool
  depthMask : Bool

-- =============================================================
-- Theorems: Enable/Disable
-- =============================================================

theorem blend_alpha_correct :
    blendMode RL_BLEND_ALPHA = { enabled := true, srcRGB := GL_SRC_ALPHA, dstRGB := GL_ONE_MINUS_SRC_ALPHA, equation := GL_FUNC_ADD } := by
  unfold blendMode RL_BLEND_ALPHA; rfl

theorem blend_additive_correct :
    blendMode RL_BLEND_ADDITIVE = { enabled := true, srcRGB := GL_SRC_ALPHA, dstRGB := GL_ONE, equation := GL_FUNC_ADD } := by
  unfold blendMode RL_BLEND_ADDITIVE; rfl

theorem blend_multiplied_correct :
    blendMode RL_BLEND_MULTIPLIED = { enabled := true, srcRGB := GL_DST_COLOR, dstRGB := GL_ONE_MINUS_SRC_ALPHA, equation := GL_FUNC_ADD } := by
  unfold blendMode RL_BLEND_MULTIPLIED; rfl

theorem blend_add_colors_correct :
    blendMode RL_BLEND_ADD_COLORS = { enabled := true, srcRGB := GL_ONE, dstRGB := GL_ONE, equation := GL_FUNC_ADD } := by
  unfold blendMode RL_BLEND_ADD_COLORS; rfl

theorem blend_subtract_colors_correct :
    blendMode RL_BLEND_SUBTRACT_COLORS = { enabled := true, srcRGB := GL_ONE, dstRGB := GL_ONE, equation := GL_FUNC_SUBTRACT } := by
  unfold blendMode RL_BLEND_SUBTRACT_COLORS; rfl

theorem blend_alpha_premultiply_correct :
    blendMode RL_BLEND_ALPHA_PREMULTIPLY = { enabled := true, srcRGB := GL_ONE, dstRGB := GL_ONE_MINUS_SRC_ALPHA, equation := GL_FUNC_ADD } := by
  unfold blendMode RL_BLEND_ALPHA_PREMULTIPLY; rfl

theorem blend_custom_enables : (blendMode RL_BLEND_CUSTOM).enabled = true := by
  unfold blendMode RL_BLEND_CUSTOM; rfl

theorem blend_custom_separate_enables : (blendMode RL_BLEND_CUSTOM_SEPARATE).enabled = true := by
  unfold blendMode RL_BLEND_CUSTOM_SEPARATE; rfl

theorem blend_default_disables : (blendMode 99).enabled = false := by
  unfold blendMode; rfl

theorem blend_alpha_src_rgb : (blendMode RL_BLEND_ALPHA).srcRGB = GL_SRC_ALPHA := by
  unfold blendMode RL_BLEND_ALPHA; rfl

theorem blend_alpha_dst_rgb : (blendMode RL_BLEND_ALPHA).dstRGB = GL_ONE_MINUS_SRC_ALPHA := by
  unfold blendMode RL_BLEND_ALPHA; rfl

theorem blend_alpha_equation : (blendMode RL_BLEND_ALPHA).equation = GL_FUNC_ADD := by
  unfold blendMode RL_BLEND_ALPHA; rfl

theorem blend_subtract_equation : (blendMode RL_BLEND_SUBTRACT_COLORS).equation = GL_FUNC_SUBTRACT := by
  unfold blendMode RL_BLEND_SUBTRACT_COLORS; rfl

end GxProofs.RhiState
