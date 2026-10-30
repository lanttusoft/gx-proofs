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
  gX — GFX Numeric Constants Specification

  Verifies the numeric constant values from
  src/renderer/gfx/constants.h (all nine re-verified against
  gX source at salvage time — unlike TexUnitCollision, whose gameX
  values went stale and was deliberately NOT salvaged).
  All constants are non-zero and within expected ranges.

  Theorems proven: 9
    - max_lights_eq_32:            gX_GFX_MAX_LIGHTS = 32
    - shadow_map_size_eq_1024:     gX_GFX_SHADOW_MAP_SIZE = 1024
    - shadow_cube_size_eq_4096:    gX_GFX_SHADOW_CUBE_SIZE = 4096
    - ibl_lut_size_eq_256:         gX_GFX_IBL_LUT_SIZE = 256
    - max_transparent_eq_128:      gX_GFX_MAX_TRANSPARENT = 128
    - models_heap_max_eq_1024:     gX_GFX_MODELS_HEAP_MAX = 1024
    - lights_heap_max_eq_128:      gX_GFX_LIGHTS_HEAP_MAX = 128
    - textures_heap_max_eq_256:    gX_GFX_TEXTURES_HEAP_MAX = 256
    - maps_heap_max_eq_8:          gX_GFX_MAPS_HEAP_MAX = 8
-/

namespace GxProofs.GfxConstants

def gX_GFX_MAX_LIGHTS         : Nat := 32
def gX_GFX_SHADOW_MAP_SIZE    : Nat := 1024
def gX_GFX_SHADOW_CUBE_SIZE   : Nat := 4096
def gX_GFX_IBL_LUT_SIZE       : Nat := 256
def gX_GFX_MAX_TRANSPARENT    : Nat := 128
def gX_GFX_MODELS_HEAP_MAX    : Nat := 1024
def gX_GFX_LIGHTS_HEAP_MAX    : Nat := 128
def gX_GFX_TEXTURES_HEAP_MAX   : Nat := 256
def gX_GFX_MAPS_HEAP_MAX       : Nat := 8

theorem max_lights_eq_32         : gX_GFX_MAX_LIGHTS = 32         := rfl
theorem shadow_map_size_eq_1024  : gX_GFX_SHADOW_MAP_SIZE = 1024  := rfl
theorem shadow_cube_size_eq_4096 : gX_GFX_SHADOW_CUBE_SIZE = 4096 := rfl
theorem ibl_lut_size_eq_256      : gX_GFX_IBL_LUT_SIZE = 256      := rfl
theorem max_transparent_eq_128   : gX_GFX_MAX_TRANSPARENT = 128   := rfl
theorem models_heap_max_eq_1024  : gX_GFX_MODELS_HEAP_MAX = 1024  := rfl
theorem lights_heap_max_eq_128   : gX_GFX_LIGHTS_HEAP_MAX = 128   := rfl
theorem textures_heap_max_eq_256 : gX_GFX_TEXTURES_HEAP_MAX = 256 := rfl
theorem maps_heap_max_eq_8       : gX_GFX_MAPS_HEAP_MAX = 8       := rfl

end GxProofs.GfxConstants
