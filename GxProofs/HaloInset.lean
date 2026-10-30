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
  gX — Marker halo/core nesting specification

  Models the selection-marker geometry from
  src/tools/editor/editor.cpp (marker draw): the dark halo rect
  is expanded 1px per side (4px stroke), the light core rect is inset
  2px per side (2px stroke), because coplanar same-depth strokes lose
  to depth-test order and the second one vanishes (commit a838f51).

  One axis suffices — X and Y instantiate identically; the wash fill
  spans the unmodified rect and needs no invariant.

  Rasterization itself is ImGui's domain (verified headless, not
  proven). What is proven here is the structural contract any future
  "vanishing stroke" report must satisfy: strict nesting with a 3px
  separation budget per side, plus the degenerate guard — below 4px
  wide the inset edges cross and the core rect inverts, which is the
  one geometric way this marker can still break.

  Theorems proven: 5
    - core_strict_left:    halo edge sits strictly outside core edge
    - core_strict_right:   same on the far side
    - separation_gap:      3px budget no ≤2px-half-width stroke can bridge
    - inset_wellformed:    width ≥ 4 keeps the core rect ordered
    - degenerate_inverts:  width < 4 crosses the inset edges (the guard)
-/

namespace GxProofs.HaloInset

-- 1. Near side: halo edge (x0-1) strictly outside core edge (x0+2).
-- Needs x0 ≥ 1 (Nat truncation); screen rects at the viewport edge
-- carry the viewport offset, and the degenerate x0 = 0 case is what
-- the guard theorems below are for.
theorem core_strict_left (x0 : Nat) (h : 1 ≤ x0) : x0 - 1 < x0 + 2 := by
  omega

-- 2. Far side: core edge (x1-2) strictly inside halo edge (x1+1).
-- Holds even under Nat truncation.
theorem core_strict_right (x1 : Nat) : x1 - 2 < x1 + 1 := by
  omega

-- 3. Separation budget: 3px between halo and core centerlines, so a
-- halo stroke reaching ≤ 2px inward and a core stroke reaching ≤ 1px
-- outward can never share a pixel.
theorem separation_gap (x0 : Nat) (h : 1 ≤ x0) : x0 + 2 - (x0 - 1) = 3 := by
  omega

-- 4. Well-formed: rects at least 4px wide keep the inset ordered.
theorem inset_wellformed (x0 x1 : Nat) (h : x0 + 4 ≤ x1) :
    x0 + 2 ≤ x1 - 2 := by
  omega

-- 5. Degenerate guard: below 4px the inset inverts — any future fix
-- for tiny-element markers must clamp before insetting, not after.
theorem degenerate_inverts (x0 x1 : Nat) (h : x1 < x0 + 4) :
    x1 - 2 < x0 + 2 := by
  omega
