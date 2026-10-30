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
  gX — Quality Preset Cascade Specification

  Models gX_RendererGFX_ApplyQualityPreset from
  src/renderer/gfx/load.c:408 (table re-verified).

  Salvage adaptations: filter codes corrected to gX's
  gX_TEXTUREFILTER enum (POINT=0, so BILINEAR=1, TRILINEAR=2,
  ANISO_4X=3, ANISO_16X=5 — the gameX original omitted POINT and
  the 8X slot); the dead non-prime applyPreset dropped; the
  out-of-range theorem dropped because gX SATURATES (clamps to
  [0,3]) while gameX defaulted to preset 0 — only inputs 0..3
  are modeled, not contradicted.

  Theorems proven: 4 (one per preset)
-/

namespace GxProofs.QualityPreset

def FILTER_BILINEAR       : Nat := 1
def FILTER_TRILINEAR      : Nat := 2
def FILTER_ANISOTROPIC_4X  : Nat := 3
def FILTER_ANISOTROPIC_16X : Nat := 5

def SHADER_LOW  : Nat := 0
def SHADER_MED  : Nat := 1
def SHADER_HIGH : Nat := 2

def MSAA_OFF : Nat := 0
def MSAA_4X  : Nat := 4

structure Preset where
  textureFilter : Nat
  shaderQuality : Nat
  msaaLevel     : Nat
  mipmapBias    : Float

-- Match 0-3 explicitly (gX clamps inputs to [0,3] in C;
-- out-of-range behavior lives in the clamp, unmodeled here).
def applyPreset' (preset : Nat) : Preset :=
  match preset with
  | 0 => { textureFilter := FILTER_BILINEAR,       shaderQuality := SHADER_LOW,  msaaLevel := MSAA_OFF, mipmapBias := 0.0 }
  | 1 => { textureFilter := FILTER_TRILINEAR,       shaderQuality := SHADER_MED,  msaaLevel := MSAA_OFF, mipmapBias := 0.0 }
  | 2 => { textureFilter := FILTER_ANISOTROPIC_4X,  shaderQuality := SHADER_HIGH, msaaLevel := MSAA_OFF, mipmapBias := 0.0 }
  | 3 => { textureFilter := FILTER_ANISOTROPIC_16X, shaderQuality := SHADER_HIGH, msaaLevel := MSAA_4X,  mipmapBias := -0.5 }
  | _ => { textureFilter := FILTER_BILINEAR,       shaderQuality := SHADER_LOW,  msaaLevel := MSAA_OFF, mipmapBias := 0.0 }

-- ------ Theorems ------

theorem preset_0_low : applyPreset' 0 = {
    textureFilter := FILTER_BILINEAR, shaderQuality := SHADER_LOW, msaaLevel := MSAA_OFF, mipmapBias := 0.0 } := by
  unfold applyPreset'; simp

theorem preset_1_medium : applyPreset' 1 = {
    textureFilter := FILTER_TRILINEAR, shaderQuality := SHADER_MED, msaaLevel := MSAA_OFF, mipmapBias := 0.0 } := by
  unfold applyPreset'; simp

theorem preset_2_high : applyPreset' 2 = {
    textureFilter := FILTER_ANISOTROPIC_4X, shaderQuality := SHADER_HIGH, msaaLevel := MSAA_OFF, mipmapBias := 0.0 } := by
  unfold applyPreset'; simp

theorem preset_3_ultra : applyPreset' 3 = {
    textureFilter := FILTER_ANISOTROPIC_16X, shaderQuality := SHADER_HIGH, msaaLevel := MSAA_4X, mipmapBias := -0.5 } := by
  unfold applyPreset'; simp

end GxProofs.QualityPreset
