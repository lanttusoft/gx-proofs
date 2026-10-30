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
  gX — Dock engage-chain specification (Mathlib tier)

  Models Dock_Update's engage path in src/gui/gui.c: widen to
  16:9 clamped to the monitor, measure margins, allow a feasible game
  shrink (scale ≥ 0.75) to reach them, engage iff the final margin
  clears 200px — else overlay fallback (return, no widen).

  Proven here:
  - the engaged window is always exactly 16:9 through every clamp
    combination (unconditional — pure algebra, no hypotheses);
  - the forced-220 margin is honest: shrinking by (tw-440)/gw leaves
    exactly 220px margins, so the forcing is a measurement, not a lie;
  - the 200px gate buys feasibility for real game widths (gw ≥ 160):
    measured margins that big always admit a ≥ 0.75 shrink — which is
    what GfxViewport.width_fit_of_feasible consumes, completing the
    engage→fit chain end to end;
  - every engagement is justified: measured margins or shrunk
    margins, never neither (the "dock engaged when it shouldn't"
    class has exactly two places to look, both in the inputs).

  Theorems proven: 4
    - aspect_invariant:   engaged window always exactly 16:9
    - shrink_margin_exact: the feasible shrink leaves exactly 220px
    - gate_sufficient:    200px measured ⇒ shrink feasible (gw ≥ 160)
    - engage_justified:   engage ⇒ measured ∨ shrunk justification
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.EngageDock

-- Monitor clamps: widen to 16:9, then clamp width, then height.
-- Each clamp recomputes the other axis to hold the ratio.
-- (No let-bindings: split_ifs must see the conditions.)
noncomputable def clampW (th monW : ℝ) : ℝ × ℝ :=
  if th * 16 / 9 > monW - 32 then
    (monW - 32, (monW - 32) * 9 / 16)
  else (th * 16 / 9, th)

noncomputable def clampH (tw th monH : ℝ) : ℝ × ℝ :=
  if th > monH - 64 then ((monH - 64) * 16 / 9, monH - 64) else (tw, th)

noncomputable def engageSize (th monW monH : ℝ) : ℝ × ℝ :=
  clampH (clampW th monW).1 (clampW th monW).2 monH

-- Final margin decision: measured, or forced-220 on feasible shrink.
noncomputable def finalMargin (tw gw : ℝ) : ℝ :=
  if (tw - gw) / 2 < 220 then
    (if (tw - 440) / gw ≥ 0.75 then 220 else (tw - gw) / 2)
  else (tw - gw) / 2

noncomputable def engages (tw gw : ℝ) : Prop :=
  finalMargin tw gw ≥ 200

-- 1. The clamp chain preserves 16:9 exactly, in every combination.
theorem aspect_invariant (th monW monH : ℝ) :
    let (tw, th2) := engageSize th monW monH
    tw * 9 = th2 * 16 := by
  unfold engageSize clampW clampH
  split_ifs with h1 h2 <;> ring

-- 2. The feasible shrink is margin-honest: exactly 220px remain.
theorem shrink_margin_exact (tw gw : ℝ) (hgw : 0 < gw) :
    (tw - gw * ((tw - 440) / gw)) / 2 = 220 := by
  have e : gw * ((tw - 440) / gw) = tw - 440 := by field_simp
  linarith

-- 3. The 200px gate buys shrink feasibility (real game widths).
theorem gate_sufficient (tw gw : ℝ) (hgw : 0 < gw) (hgw2 : 160 ≤ gw)
    (h : (tw - gw) / 2 ≥ 200) : (tw - 440) / gw ≥ 0.75 := by
  rw [ge_iff_le, le_div_iff₀ hgw]
  linarith

-- 4. Every engagement is justified by measured or shrunk margins.
theorem engage_justified (tw gw : ℝ) (h : engages tw gw) :
    (tw - gw) / 2 ≥ 200 ∨ (tw - 440) / gw ≥ 0.75 := by
  unfold engages finalMargin at h
  split_ifs at h with h1 h2
  · exact Or.inr h2
  · exact Or.inl h
  · push_neg at h1
    exact Or.inl (by linarith)
