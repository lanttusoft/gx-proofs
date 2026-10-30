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
  gX — Dock close-restore tolerance specification

  Models the close branch of Dock_Update in src/gui/gui.c: on
  undock, the drift dw/dh against the recorded dock size is measured;
  the pre-dock size is restored iff a pre-dock size exists AND both
  drifts are within 8px (WM decorations and rounding report back
  slightly off the requested size). Otherwise the current size stands
  (the user resized while docked — their size wins).

  One axis suffices — W and H instantiate identically and the branch
  conjoins them.

  Proven here are all four branch outcomes, i.e. both halves of the
  v0.6.11 hardening: small drift restores (no reopen creep) and large
  drift keeps the user's size (dock close never steals a resize).

  Theorems proven: 4
    - untouched_restores:   exact match restores pre-dock size
    - small_drift_restores: drift within 8px restores (WM tolerance)
    - user_resize_kept:     drift past 8px keeps the current size
    - no_pre_no_restore:    no recorded size means nothing to restore
-/

namespace GxProofs.DockRestore

-- Close-branch decision on one axis (gX_I32 pixel math).
def closeW (curW dockW preW : Int) : Int :=
  if 0 < preW ∧ Int.natAbs (curW - dockW) ≤ 8 then preW else curW

-- 1. Untouched window restores the pre-dock size exactly.
theorem untouched_restores (d p : Int) (h : 0 < p) : closeW d d p = p := by
  have h8 : Int.natAbs (d - d) ≤ 8 := by simp
  have hc : (0 < p ∧ Int.natAbs (d - d) ≤ 8) := ⟨h, h8⟩
  simp [closeW, hc]

-- 2. WM-decoration drift (≤ 8px) still restores.
theorem small_drift_restores (c d p : Int) (h : 0 < p)
    (hle : Int.natAbs (c - d) ≤ 8) : closeW c d p = p := by
  simp [closeW, h, hle]

-- 3. A real user resize survives dock close.
theorem user_resize_kept (c d p : Int)
    (hgt : 8 < Int.natAbs (c - d)) : closeW c d p = c := by
  have hle : ¬ Int.natAbs (c - d) ≤ 8 := by omega
  simp [closeW, hle]

-- 4. No recorded pre-dock size: current size stands (first-run safe).
theorem no_pre_no_restore (c d : Int) : closeW c d 0 = c := by
  simp [closeW]
