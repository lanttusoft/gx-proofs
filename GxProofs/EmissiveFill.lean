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
  gX — Preset-injected emission defaults-fill Specification

  Models src/renderer/gfx/model.c gX_RendererGFX_Model_Load's
  preset-binding loop: when a preset binds a texture to
  gX_MATERIAL_MAP_EMISSION the engine enables hasEmissiveMap and, if
  emissiveColor is still the engine default black, fills it white and
  lifts a zero emissiveFactor to 1. The shader multiplies the emission
  map by emissiveColor * emissiveFactor, so without the fill an
  injected map sampled but contributed exactly nothing (the RC
  dogfooding walk's "injected maps render black" bug). A scene-set
  emissive color survives untouched — the same precedence as the GLB
  loader's emissive defaults-fill.

  Theorems proven: 8, all by rfl/simp/decide/omega.
-/

namespace GxProofs.EmissiveFill

structure Emissive where
  r : Nat
  g : Nat
  b : Nat
  factor : Nat
deriving DecidableEq, Repr

def isBlack (c : Emissive) : Bool :=
  c.r == 0 && c.g == 0 && c.b == 0

-- The engine's defaults-fill: black color -> white, zero factor -> 1.
def fill (c : Emissive) : Emissive :=
  if isBlack c then
    { r := 255, g := 255, b := 255, factor := if c.factor = 0 then 1 else c.factor }
  else c

-- The fill only runs for a preset-injected emission map.
def onInject (injected : Bool) (c : Emissive) : Emissive :=
  if injected then fill c else c

theorem fill_black_white (c : Emissive) (h : isBlack c = true) :
    (fill c).r = 255 ∧ (fill c).g = 255 ∧ (fill c).b = 255 := by
  simp [fill, h]

theorem fill_black_factor_pos (c : Emissive) (h : isBlack c = true) :
    (fill c).factor > 0 := by
  simp [fill, h]
  split <;> omega

theorem fill_black_emits (c : Emissive) (h : isBlack c = true) :
    (fill c).r * (fill c).factor > 0 := by
  simp [fill, h]
  split <;> omega

theorem fill_preserves_color (c : Emissive) (h : isBlack c = false) :
    fill c = c := by
  simp [fill, h]

theorem fill_preserves_factor (c : Emissive) (h : isBlack c = false) :
    (fill c).factor = c.factor := by
  simp [fill, h]

theorem fill_idempotent (c : Emissive) : fill (fill c) = fill c := by
  unfold fill
  split
  · simp [isBlack]
  · rfl

theorem onInject_none (c : Emissive) : onInject false c = c := rfl

theorem onInject_injected (c : Emissive) : onInject true c = fill c := rfl

end GxProofs.EmissiveFill
