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
  gX — Viewport round-trip specification

  Models the always-map coordinate pair from src/gui/gui.c
  (gX_GUI_ScreenToGame / gX_GUI_GameToScreen, as consumed every frame by
  src/input.c:gX_Input_Update_Mouse) over one axis — X and Y
  instantiate identically.

  Nat model below keeps integer division explicit. The C mapping uses F32
  division, which may round either above or below the exact quotient; these
  Nat inequalities are not a machine-float error bound or a C correspondence
  proof.

  Scope: points inside the viewport (o ≤ p). Presses outside it are
  rejected before mapping (editor/viewport press routing), so the
  round trip is only ever invoked in range.

  Theorems proven: 5
    - undocked_identity_toGame:    full-window box ⇒ s2g is identity
    - undocked_identity_toScreen:  full-window box ⇒ g2s is identity
    - right_edge_toScreen:         gameW maps exactly onto vpW (scale consistency)
    - right_edge_toGame:           vp edge maps exactly onto gameW
    - roundtrip_upper:             g2s(s2g(p)) ≤ p (never overshoots)
-/

namespace GxProofs.ViewportRoundtrip

-- Screen→game on one axis: (p - o) * n / d  (n = gameW, d = vpW).
def toGame (p o n d : Nat) : Nat := (p - o) * n / d

-- Game→screen on one axis: o + g * d / n  (d = vpW, n = gameW).
def toScreen (g o n d : Nat) : Nat := o + g * d / n

-- 1. Undocked full-window box (o = 0, vpW = gameW): s2g is identity.
theorem undocked_identity_toGame (sx G : Nat) (hG : 0 < G) :
    toGame sx 0 G G = sx := by
  unfold toGame
  rw [Nat.sub_zero, Nat.mul_div_cancel _ hG]

-- 2. Undocked full-window box: g2s is identity.
theorem undocked_identity_toScreen (gx G : Nat) (hG : 0 < G) :
    toScreen gx 0 G G = gx := by
  unfold toScreen
  rw [Nat.mul_div_cancel _ hG, Nat.zero_add]

-- 3. Right/bottom edge: gameW maps exactly onto vpW (scale consistency).
theorem right_edge_toScreen (o n d : Nat) (hn : 0 < n) :
    toScreen n o n d = o + d := by
  unfold toScreen
  rw [Nat.mul_comm n d, Nat.mul_div_cancel _ hn]

-- 4. Right/bottom edge: viewport edge maps exactly onto gameW.
theorem right_edge_toGame (o n d : Nat) (hd : 0 < d) :
    toGame (o + d) o n d = n := by
  unfold toGame
  rw [Nat.add_sub_cancel_left, Nat.mul_comm d n, Nat.mul_div_cancel _ hd]

-- 5. Round trip never overshoots (for in-viewport points). Needs only
--   gameW > 0 — truncated-division bounds hold even at vpW = 0.
theorem roundtrip_upper (p o G W : Nat) (hG : 0 < G) (hle : o ≤ p) :
    toScreen (toGame p o G W) o G W ≤ p := by
  unfold toScreen toGame
  have h1 : (p - o) * G / W * W ≤ (p - o) * G := Nat.div_mul_le_self _ _
  have h2 : (p - o) * G / W * W / G ≤ (p - o) * G / G := Nat.div_le_div_right h1
  rw [Nat.mul_div_cancel _ hG] at h2
  calc o + (p - o) * G / W * W / G
      ≤ o + (p - o) := Nat.add_le_add_left h2 _
    _ = p := Nat.add_sub_cancel' hle
