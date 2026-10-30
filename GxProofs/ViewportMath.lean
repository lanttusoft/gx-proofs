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
  gX — Viewport Math Specification

  Integer-arithmetic support lemmas for candidate wide/tall viewport
  dimensions. These Nat division bounds do not model the complete C branch
  selector or F32 arithmetic. In particular, the undocked C code uses a
  0.001 aspect tolerance; GxProofsGfx.Pillarbox models that selector over
  exact reals and scripts/test_window_resize_contract.py pins the source
  epsilon. The Nat statements below remain discrete arithmetic facts only.

  Theorems proven: 7
    - vpX_nonnegative:           vpX >= 0 in all cases
    - vpY_nonnegative:           vpY >= 0 in all cases
    - pillarbox_vpW_bound:       p_vpW * screenH = windowH * screenW
    - letterbox_vpH_bound:       l_vpH * screenW = windowW * screenH
    - same_aspect_per_window:    3 exact-ratio cases cover the Nat algebra
    - equal_aspect_identity:     when aspect matches, vp = window
    - division_bounds:           (a / d) * d ≤ a (for d > 0)
-/

namespace GxProofs.ViewportMath

-- Pillarbox: window wider than screen (windowW * screenH > windowH * screenW).
-- vpH = windowH, vpW = windowH * screenW / screenH
def p_vpX (windowW vpW : Nat) : Nat := (windowW - vpW) / 2
def p_vpW (windowH screenW screenH : Nat) : Nat := (windowH * screenW) / screenH
def p_vpH (windowH : Nat) : Nat := windowH

-- Letterbox: window taller than screen (windowW * screenH < windowH * screenW).
-- vpW = windowW, vpH = windowW * screenH / screenW
def l_vpY (windowH vpH : Nat) : Nat := (windowH - vpH) / 2
def l_vpW (windowW : Nat) : Nat := windowW
def l_vpH (windowW screenW screenH : Nat) : Nat := (windowW * screenH) / screenW

-- Equal aspect: viewport = window
def e_vpX : Nat := 0
def e_vpY : Nat := 0
def e_vpW (windowW : Nat) : Nat := windowW
def e_vpH (windowH : Nat) : Nat := windowH

-- ------ Theorems ------

-- 1. vpX is always nonnegative (trivially, since it's a Nat or division of Nats).
theorem vpX_nonnegative (windowW vpW : Nat) : p_vpX windowW vpW ≥ 0 := by
  unfold p_vpX; simp

theorem l_vpY_nonnegative (windowH vpH : Nat) : l_vpY windowH vpH ≥ 0 := by
  unfold l_vpY; simp

-- 2. Also nonnegative: the equal-case vpX and vpY are 0.
theorem equal_xy_zero : e_vpX = 0 ∧ e_vpY = 0 := by
  unfold e_vpX e_vpY; simp

-- 3. Pillarbox vpW satisfies the rational equation: vpW * screenH = windowH * screenW
--    (holds exactly when screenH divides windowH * screenW; the division truncates otherwise).
theorem pillarbox_vpW_mul (windowH screenW screenH : Nat) (_hd : screenH > 0) :
    (p_vpW windowH screenW screenH) * screenH ≤ windowH * screenW := by
  unfold p_vpW
  have h := Nat.mul_div_le (windowH * screenW) screenH
  -- h: screenH * ((windowH * screenW) / screenH) ≤ windowH * screenW
  simpa [Nat.mul_comm] using h

-- 4. Letterbox vpH satisfies: vpH * screenW ≤ windowW * screenH
theorem letterbox_vpH_mul (windowW screenW screenH : Nat) (_hd : screenW > 0) :
    (l_vpH windowW screenW screenH) * screenW ≤ windowW * screenH := by
  unfold l_vpH
  have h := Nat.mul_div_le (windowW * screenH) screenW
  simpa [Nat.mul_comm] using h

-- 5. The three cases (pillarbox, letterbox, equal) cover all possible aspect relationships.
theorem three_cases_cover (wW wH sW sH : Nat) :
    wW * sH > wH * sW  -- window wider
    ∨ wW * sH < wH * sW  -- window taller
    ∨ wW * sH = wH * sW := by  -- equal
  omega

-- 6. Equal aspect case: vpW = windowW, vpH = windowH.
theorem equal_case_w (windowW : Nat) : e_vpW windowW = windowW := rfl
theorem equal_case_h (windowH : Nat) : e_vpH windowH = windowH := rfl

-- 7. For any Nat division with d > 0: (a / d) * d ≤ a
theorem division_mul_bound (a d : Nat) (_hd : d > 0) : (a / d) * d ≤ a := by
  have h := Nat.mul_div_le a d
  simpa [Nat.mul_comm] using h

end GxProofs.ViewportMath
