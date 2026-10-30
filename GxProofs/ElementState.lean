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
  gX — GUI Element State Machine Specification
  Invariant: DISABLED forces all Runtime flags off.
  onLeave clears all Runtime flags unconditionally.
  See src/gui/element/element.c, struct.h:gX_GUI_Element_State.
  Salvage note: gameX modeled scrollable/scrolled flags that do not
  exist in gX's struct (no SCROLLABLE bit); the scroll conjuncts were
  dropped, the remaining six theorems re-verified below.
-/

namespace GxProofs.ElementState

structure Config where
  hoverable   : Bool
  clickableL  : Bool
  pressableL   : Bool
  toggleable  : Bool
  disabled    : Bool
deriving DecidableEq

structure Runtime where
  hovered     : Bool
  clickedL    : Bool
  pressedL    : Bool
  toggled     : Bool
deriving DecidableEq

def clearRt : Runtime :=
  { hovered := false, clickedL := false, pressedL := false,
    toggled := false }

def onLeave (_rt : Runtime) : Runtime := clearRt

def valid (cfg : Config) (rt : Runtime) : Prop :=
  (cfg.hoverable  = true ∨ rt.hovered  = false)
  ∧ (cfg.clickableL = true ∨ rt.clickedL = false)
  ∧ (cfg.pressableL  = true ∨ rt.pressedL = false)
  ∧ (cfg.toggleable = true ∨ rt.toggled = false)
  ∧ (cfg.disabled = true → rt = clearRt)

theorem hovered_implies_hoverable (cfg : Config) (rt : Runtime)
    (h : valid cfg rt) (h_hov : rt.hovered = true) : cfg.hoverable = true := by
  rcases h with ⟨h_hv, _, _, _, _⟩
  rcases h_hv with (h_ho | h_nhov)
  · exact h_ho
  · exfalso; exact (by
      have : true = false := h_hov.symm.trans h_nhov
      exact (by decide : true ≠ false) this)

theorem clicked_implies_clickable (cfg : Config) (rt : Runtime)
    (h : valid cfg rt) (h_clk : rt.clickedL = true) : cfg.clickableL = true := by
  rcases h with ⟨_, h_cl, _, _, _⟩
  rcases h_cl with (h_cl' | h_nclk)
  · exact h_cl'
  · exfalso; exact (by
      have : true = false := h_clk.symm.trans h_nclk
      exact (by decide : true ≠ false) this)

theorem pressed_implies_pressable (cfg : Config) (rt : Runtime)
    (h : valid cfg rt) (h_prs : rt.pressedL = true) : cfg.pressableL = true := by
  rcases h with ⟨_, _, h_pr, _, _⟩
  rcases h_pr with (h_pr' | h_nprs)
  · exact h_pr'
  · exfalso; exact (by
      have : true = false := h_prs.symm.trans h_nprs
      exact (by decide : true ≠ false) this)

theorem toggled_implies_toggleable (cfg : Config) (rt : Runtime)
    (h : valid cfg rt) (h_tog : rt.toggled = true) : cfg.toggleable = true := by
  rcases h with ⟨_, _, _, h_tg, _⟩
  rcases h_tg with (h_tg' | h_ntog)
  · exact h_tg'
  · exfalso; exact (by
      have : true = false := h_tog.symm.trans h_ntog
      exact (by decide : true ≠ false) this)

theorem disabled_requires_runtime_off (cfg : Config) (rt : Runtime)
    (h : valid cfg rt) (hd : cfg.disabled = true) : rt = clearRt := by
  rcases h with ⟨_, _, _, _, h_dis⟩; exact h_dis hd

theorem onleave_clears_all (rt : Runtime) :
    (onLeave rt).hovered = false ∧ (onLeave rt).clickedL = false
    ∧ (onLeave rt).pressedL = false ∧ (onLeave rt).toggled = false := by
  unfold onLeave clearRt; simp

end GxProofs.ElementState
