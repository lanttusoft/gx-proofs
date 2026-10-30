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
  gX — PCG32 deterministic random Specification

  Models src/gxmath/random.c (gX_Random32_*): engine draws come from an
  explicit PCG32 stream instead of libc rand(), so seeded captures and
  audits are reproducible on every platform, and every consumer can own
  its stream instead of sharing one global sequence (the "rand()
  pollution" the weather/splat locals used to work around).

  The sequence itself is pinned numerically by the math pass (published
  pcg32-demo vectors); this spec pins the structural guarantees the API
  relies on.

  Theorems proven: 5, all core tactics (no Mathlib).
-/

namespace GxProofs.Random32

-- The stream normalization: PCG requires an odd increment.
def incOf (stream : Nat) : Nat := stream * 2 + 1

theorem inc_odd (stream : Nat) : incOf stream % 2 = 1 := by
  unfold incOf
  omega

-- Distinct streams produce distinct increments (so they diverge).
theorem streams_diverge (s1 s2 : Nat) (h : s1 ≠ s2) : incOf s1 ≠ incOf s2 := by
  unfold incOf
  omega

-- The unbiased bounded draw: an accepted value reduced modulo the bound.
theorem bounded_lt (v bound : Nat) (h : 0 < bound) : v % bound < bound :=
  Nat.mod_lt v h

-- A draw never returns the bound itself (the API's [0, bound) contract).
theorem bounded_ne_bound (v bound : Nat) (h : 0 < bound) : v % bound ≠ bound := by
  have := Nat.mod_lt v h
  omega

-- The float draw's mantissa: the top 24 bits of a 32-bit word are < 2^24,
-- so the [0, 1) mapping cannot reach 1.0 (C uses `v >> 8`, i.e. v / 256).
theorem f32_bits_lt (v : Nat) (h : v < 2^32) : v / 256 < 2^24 := by
  apply Nat.div_lt_of_lt_mul
  rw [show 2^24 * 256 = 2^32 by decide]
  exact h

end GxProofs.Random32
