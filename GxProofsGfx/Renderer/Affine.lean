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
  gX — Exact coordinate-map specification (Mathlib tier)

  The ℝ counterpart to GxProofs.ViewportRoundtrip: over the reals the
  Nat truncation bound becomes an exact round trip, which is what the
  C float code approximates (float rounding is the only remaining
  error source — the algebra itself is exact).

  Models src/gui/gui.c gX_GUI_ScreenToGame / GameToScreen on
  one axis (X and Y instantiate identically), with s > 0 the live
  viewport scale (the s ≤ 0 identity fallback is a separate degenerate
  guard, not mapped here).

  Theorems proven: 6
    - roundtrip:        g2s(s2g(p)) = p (exact, s ≠ 0)
    - roundtrip_inv:    s2g(g2s(g)) = g (exact, s ≠ 0)
    - undocked_identity: full-window box is the identity both ways
    - edge_consistent:  the far game edge lands on the far vp edge
    - fallback_identity: s ≤ 0 falls back to the identity
    - safe_total:       every call falls back or maps (no third case)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.AffineMap

-- Screen→game: (p - o) / s.
noncomputable def toGame (p o s : ℝ) : ℝ := (p - o) / s

-- Game→screen: o + g * s.
noncomputable def toScreen (g o s : ℝ) : ℝ := o + g * s

-- 1. Exact round trip screen→game→screen.
theorem roundtrip (p o s : ℝ) (hs : s ≠ 0) :
    toScreen (toGame p o s) o s = p := by
  unfold toGame toScreen
  field_simp
  ring

-- 2. Exact round trip game→screen→game.
theorem roundtrip_inv (g o s : ℝ) (hs : s ≠ 0) :
    toGame (toScreen g o s) o s = g := by
  unfold toGame toScreen
  field_simp
  ring

-- 3. Undocked full-window box (o = 0, s = 1) is the identity.
theorem undocked_identity (p : ℝ) :
    toGame p 0 1 = p ∧ toScreen p 0 1 = p := by
  constructor <;> simp only [toGame, toScreen] <;> ring

-- 4. Edge consistency: the far game edge maps onto the far viewport
-- edge (scale applied once, offset applied once, no drift).
theorem edge_consistent (o gw s : ℝ) (hs : s ≠ 0) :
    toGame (o + gw * s) o s = gw := by
  unfold toGame
  field_simp
  ring

-- Degenerate guard: s ≤ 0 falls back to the identity (C returns its
-- input when the viewport scale is dead).
noncomputable def safeGame (p o s : ℝ) : ℝ :=
  if s ≤ 0 then p else toGame p o s

noncomputable def safeScreen (g o s : ℝ) : ℝ :=
  if s ≤ 0 then g else toScreen g o s

-- 5. The fallback is the identity (zero-scale viewports map nothing,
-- and corrupt nothing).
theorem fallback_identity (p o s : ℝ) (h : s ≤ 0) :
    safeGame p o s = p ∧ safeScreen p o s = p := by
  constructor
  · simp [safeGame, h]
  · simp [safeScreen, h]

-- 6. Totality: every call either falls back or maps (no third case).
theorem safe_total (p o s : ℝ) :
    safeGame p o s = p ∨ safeGame p o s = toGame p o s := by
  unfold safeGame
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl
