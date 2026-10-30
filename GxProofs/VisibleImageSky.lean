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

--ai: source-grounded routing model for src/renderer/gfx/draw.c.
-- Does not prove GL resource validity, cubemap orientation, colors, or C translation.
namespace GxProofs.VisibleImageSky

structure Inputs where
  optedIn : Bool
  skyboxEnabled : Bool
  loaded : Bool
  textureValid : Bool
  shaderValid : Bool
  proceduralEnabled : Bool

def imageSelected (s : Inputs) : Bool :=
  s.optedIn && s.skyboxEnabled && s.loaded && s.textureValid && s.shaderValid

def proceduralSelected (s : Inputs) : Bool :=
  s.proceduralEnabled && s.shaderValid

def drawsBackground (s : Inputs) : Bool :=
  proceduralSelected s || imageSelected s

--ai: capture/LUT helpers pass false; the visible scene draw passes its selector.
inductive Pass where
  | scene | cubeCapture | skyLut
  deriving DecidableEq

def selectorFor (p : Pass) (s : Inputs) : Bool :=
  match p with
  | .scene => imageSelected s
  | .cubeCapture | .skyLut => false

def uploadSelector (_previous : Bool) (p : Pass) (s : Inputs) : Bool :=
  selectorFor p s

theorem default_off (s : Inputs) :
    imageSelected { s with optedIn := false } = false := by
  simp [imageSelected]

theorem missing_image_fallback (s : Inputs) :
    drawsBackground { s with textureValid := false } = proceduralSelected s := by
  simp [drawsBackground, imageSelected, proceduralSelected]

theorem unloaded_image_fallback (s : Inputs) :
    drawsBackground { s with loaded := false } = proceduralSelected s := by
  simp [drawsBackground, imageSelected, proceduralSelected]

theorem invalid_shader_no_draw (s : Inputs) :
    drawsBackground { s with shaderValid := false } = false := by
  simp [drawsBackground, imageSelected, proceduralSelected]

theorem cube_capture_independent (s : Inputs) :
    selectorFor .cubeCapture s = false := rfl

theorem sky_lut_independent (s : Inputs) :
    selectorFor .skyLut s = false := rfl

theorem no_selector_leak (previous : Bool) (s : Inputs) :
    uploadSelector previous .cubeCapture s = false := rfl

theorem upload_overwrites_previous (a b : Bool) (p : Pass) (s : Inputs) :
    uploadSelector a p s = uploadSelector b p s := rfl

end GxProofs.VisibleImageSky
