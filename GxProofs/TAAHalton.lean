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
  gX — TAA Halton Jitter Sequence
-/

namespace GxProofs.TAAHalton

--ai: natural-number arithmetic only; this does not certify C overflow, lifecycle resets, or jitter bounds.
-- An individual abstract increment is strictly increasing, not the entire resettable runtime trace.
theorem frameIndex_monotonic (frameIndex : Nat) : frameIndex < frameIndex + 1 := by
  omega

-- The Halton radical inverse loop terminates because i decreases each iteration
-- i / b < i when i > 0 and b ≥ 2
theorem loop_terminates (i b : Nat) (h : i > 0) (hb : b ≥ 2) : i / b < i := by
  exact Nat.div_lt_self h hb

end GxProofs.TAAHalton
