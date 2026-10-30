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
  gX — RHI FBO State Tracker Specification

  Models the internal FBO binding state machine in src/rhi/rhi_fbo.c.

  The tracker maintains two Nat values (drawFbo, readFbo):
  - 0 = default framebuffer
  - MAX_U32 (= 2^32-1) = invalidated sentinel (from InvalidateFBO)

  All Bind/Unbind operations have an early-out optimization: if the
  requested state already matches, the GL call is skipped. This is
   modeled at tracker level — every function checks the current state before
   returning a new one. Valid GL names and cache/driver coherence are caller
   assumptions; GL error behavior is not modeled. Public query contracts below
   distinguish raw cached fields from sentinel-clamped and resolved bindings.

  Theorems proven: 19
    - bindFbo_sets_both:          BindFBO(x) → draw = x ∧ read = x
    - bindFbo_idempotent:         BindFBO(x); BindFBO(x) = BindFBO(x)
    - bindFbo_skip_if_match:      draw = x ∧ read = x → BindFBO(x) is no-op
    - bindDraw_sets_draw:         BindDrawFBO(x) → draw = x
    - bindDraw_preserves_read:    BindDrawFBO(x) → read unchanged
    - bindDraw_skip_if_match:     draw = x → BindDrawFBO(x) is no-op
    - bindRead_sets_read:         BindReadFBO(x) → read = x
    - bindRead_preserves_draw:    BindReadFBO(x) → draw unchanged
    - bindRead_skip_if_match:     read = x → BindReadFBO(x) is no-op
    - unbind_clears_both:         UnbindFBO() → draw = 0 ∧ read = 0
    - unbind_idempotent:          draw = 0 ∧ read = 0 → UnbindFBO() is no-op
    - invalidate_sets_sentinel:   InvalidateFBO() → draw = MAX_U32 ∧ read = MAX_U32
    - bind_after_invalidate:      after Invalidate, BindFBO(x) always sets (x, x)
    - delete_clears_tracker:      getDraw = x → read = x → delete x → getDraw = 0
    - delete_zero_noop:           delete 0 is no-op
    - delete_nonzero_clears_match: delete x clears draw/read only if they equal x
-/

namespace GxProofs.RhiFbo

-- The sentinel value set by InvalidateFBO (maps from (gX_RHI_FBO)-1 = MAX_U32)
def MAX_U32 : Nat := 4294967295

-- The tracker state: (drawFbo, readFbo)
-- 0 = default framebuffer, MAX_U32 = invalidated
structure State where
  draw : Nat
  read : Nat
deriving DecidableEq

-- All-zero initial state (engine start, nothing bound)
def empty : State := { draw := 0, read := 0 }

--ai: raw tracker accessors for the algebra below, NOT the public sentinel-clamping C queries.
def getDraw (s : State) : Nat := s.draw
def getRead (s : State) : Nat := s.read

-- =============================================================
-- Primitive operations (model rhi_fbo.c one-to-one)
-- =============================================================

-- gX_RHI_BindFBO(fbo): set both draw and read to fbo.
--   Optimized: skip GL call if both already match.
def bindFbo (s : State) (x : Nat) : State :=
  if s.draw = x ∧ s.read = x then s
  else { draw := x, read := x }

-- gX_RHI_BindDrawFBO(fbo): set draw to fbo only.
--   Optimized: skip if draw already matches.
def bindDrawFbo (s : State) (x : Nat) : State :=
  if s.draw = x then s
  else { draw := x, read := s.read }

-- gX_RHI_BindReadFBO(fbo): set read to fbo only.
--   Optimized: skip if read already matches.
def bindReadFbo (s : State) (x : Nat) : State :=
  if s.read = x then s
  else { draw := s.draw, read := x }

-- gX_RHI_UnbindFBO(): reset both to 0.
--   Optimized: skip if both already 0.
def unbindFbo (s : State) : State :=
  if s.draw = 0 ∧ s.read = 0 then s
  else { draw := 0, read := 0 }

-- gX_RHI_UnbindDrawFBO(): reset draw to 0.
--   Optimized: skip if draw already 0.
def unbindDrawFbo (s : State) : State :=
  if s.draw = 0 then s
  else { draw := 0, read := s.read }

-- gX_RHI_UnbindReadFBO(): reset read to 0.
--   Optimized: skip if read already 0.
def unbindReadFbo (s : State) : State :=
  if s.read = 0 then s
  else { draw := s.draw, read := 0 }

-- gX_RHI_InvalidateFBO(): set both to MAX_U32 sentinel.
--   No optimization — always sets (used when raylib binds outside RHI).
def invalidateFbo (_ : State) : State :=
  { draw := MAX_U32, read := MAX_U32 }

-- gX_RHI_FBO_Delete(fbo): delete an FBO.
--   If draw/read track this FBO, reset to 0. Delete(0) is no-op.
def deleteFbo (s : State) (x : Nat) : State :=
  if x = 0 then s
  else { draw := if s.draw = x then 0 else s.draw,
         read := if s.read = x then 0 else s.read }

-- =============================================================
-- Theorem 1: BindFBO sets both draw and read
-- =============================================================
theorem bindFbo_sets_both (s : State) (x : Nat) :
    getDraw (bindFbo s x) = x ∧ getRead (bindFbo s x) = x := by
  unfold bindFbo getDraw getRead
  by_cases h : s.draw = x ∧ s.read = x
  · rcases h with ⟨hd, hr⟩
    simp [hd, hr]
  · simp [h]

-- =============================================================
-- Theorem 2: BindFBO is idempotent
-- =============================================================
theorem bindFbo_idempotent (s : State) (x : Nat) :
    bindFbo (bindFbo s x) x = bindFbo s x := by
  unfold bindFbo
  by_cases h1 : s.draw = x ∧ s.read = x
  · rcases h1 with ⟨hd, hr⟩
    simp [hd, hr]
  · simp [h1]

-- =============================================================
-- Theorem 3: BindFBO is a no-op when both already match
-- =============================================================
theorem bindFbo_skip_if_match (s : State) (x : Nat)
    (hd : s.draw = x) (hr : s.read = x) : bindFbo s x = s := by
  unfold bindFbo
  simp [hd, hr]

-- =============================================================
-- Theorem 4: BindDrawFBO sets draw
-- =============================================================
theorem bindDraw_sets_draw (s : State) (x : Nat) :
    getDraw (bindDrawFbo s x) = x := by
  unfold bindDrawFbo getDraw
  by_cases h : s.draw = x
  · simp [h]
  · simp [h]

-- =============================================================
-- Theorem 5: BindDrawFBO preserves read
-- =============================================================
theorem bindDraw_preserves_read (s : State) (x : Nat) :
    getRead (bindDrawFbo s x) = getRead s := by
  unfold bindDrawFbo getRead
  by_cases h : s.draw = x
  · simp [h]
  · simp [h]

-- =============================================================
-- Theorem 6: BindDrawFBO is a no-op when draw already matches
-- =============================================================
theorem bindDraw_skip_if_match (s : State) (x : Nat)
    (h : s.draw = x) : bindDrawFbo s x = s := by
  unfold bindDrawFbo
  simp [h]

-- =============================================================
-- Theorem 7: BindReadFBO sets read
-- =============================================================
theorem bindRead_sets_read (s : State) (x : Nat) :
    getRead (bindReadFbo s x) = x := by
  unfold bindReadFbo getRead
  by_cases h : s.read = x
  · simp [h]
  · simp [h]

-- =============================================================
-- Theorem 8: BindReadFBO preserves draw
-- =============================================================
theorem bindRead_preserves_draw (s : State) (x : Nat) :
    getDraw (bindReadFbo s x) = getDraw s := by
  unfold bindReadFbo getDraw
  by_cases h : s.read = x
  · simp [h]
  · simp [h]

-- =============================================================
-- Theorem 9: BindReadFBO is a no-op when read already matches
-- =============================================================
theorem bindRead_skip_if_match (s : State) (x : Nat)
    (h : s.read = x) : bindReadFbo s x = s := by
  unfold bindReadFbo
  simp [h]

-- =============================================================
-- Theorem 10: UnbindFBO clears both draw and read to 0
-- =============================================================
theorem unbind_clears_both (s : State) :
    getDraw (unbindFbo s) = 0 ∧ getRead (unbindFbo s) = 0 := by
  unfold unbindFbo getDraw getRead
  by_cases h : s.draw = 0 ∧ s.read = 0
  · rcases h with ⟨hd, hr⟩
    simp [hd, hr]
  · simp [h]

-- =============================================================
-- Theorem 11: UnbindFBO is a no-op when both are already 0
-- =============================================================
theorem unbind_idempotent (s : State) (hd : s.draw = 0) (hr : s.read = 0) :
    unbindFbo s = s := by
  unfold unbindFbo
  simp [hd, hr]

-- =============================================================
-- Theorem 12: InvalidateFBO sets both to MAX_U32 sentinel
-- =============================================================
theorem invalidate_sets_sentinel (s : State) :
    getDraw (invalidateFbo s) = MAX_U32 ∧ getRead (invalidateFbo s) = MAX_U32 := by
  unfold invalidateFbo getDraw getRead
  simp

-- =============================================================
-- Theorem 13: After InvalidateFBO, BindFBO(x) always applies
--   (never hits the skip-optimization, since sentinel MAX_U32 ≠ x)
-- =============================================================
theorem bind_after_invalidate (s : State) (x : Nat) (h : x ≠ MAX_U32) :
    bindFbo (invalidateFbo s) x = { draw := x, read := x } := by
  unfold bindFbo invalidateFbo
  have hne : MAX_U32 ≠ x := h.symm
  simp [hne]

-- =============================================================
-- Theorem 14: Delete(0) is a no-op
-- =============================================================
theorem delete_zero_noop (s : State) : deleteFbo s 0 = s := by
  unfold deleteFbo; simp

-- =============================================================
-- Theorem 15: Delete(x) resets draw/read to 0 only if they matched x
-- =============================================================
theorem delete_nonzero_clears_match (s : State) (x : Nat) (hx : x ≠ 0) :
    getDraw (deleteFbo s x) = (if s.draw = x then 0 else s.draw) ∧
    getRead (deleteFbo s x) = (if s.read = x then 0 else s.read) := by
  unfold deleteFbo getDraw getRead
  simp [hx]

-- =============================================================
-- Theorem 16: Delete(x) clears draw when draw = x (nonzero)
-- =============================================================
theorem delete_clears_draw (s : State) (x : Nat) (hx : x ≠ 0) (hd : s.draw = x) :
    getDraw (deleteFbo s x) = 0 := by
  unfold deleteFbo getDraw
  simp [hx, hd]

-- =============================================================
-- Theorem 17: Delete(x) clears read when read = x (nonzero)
-- =============================================================
theorem delete_clears_read (s : State) (x : Nat) (hx : x ≠ 0) (hr : s.read = x) :
    getRead (deleteFbo s x) = 0 := by
  unfold deleteFbo getRead
  simp [hx, hr]

-- =============================================================
-- Theorem 18: Delete(x) preserves draw when draw ≠ x
-- =============================================================
theorem delete_preserves_draw (s : State) (x : Nat) (hd : s.draw ≠ x) :
    getDraw (deleteFbo s x) = s.draw := by
  unfold deleteFbo getDraw
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, hd]

-- =============================================================
-- Theorem 19: Delete(x) preserves read when read ≠ x
-- =============================================================
theorem delete_preserves_read (s : State) (x : Nat) (hr : s.read ≠ x) :
    getRead (deleteFbo s x) = s.read := by
  unfold deleteFbo getRead
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, hr]

--ai: mirror the public C getters and the resolved snapshot used by FBO_ColorName.
def getDrawSafe (s : State) : Nat := if s.draw = MAX_U32 then 0 else s.draw
def getReadSafe (s : State) : Nat := if s.read = MAX_U32 then 0 else s.read
def getDrawResolved (s : State) (actualDraw : Nat) : Nat :=
  if s.draw = MAX_U32 then actualDraw else s.draw

theorem invalidated_safe_queries_zero (s : State) :
    getDrawSafe (invalidateFbo s) = 0 ∧ getReadSafe (invalidateFbo s) = 0 := by
  simp [getDrawSafe, getReadSafe, invalidateFbo]

theorem invalidated_resolved_query_actual (s : State) (actualDraw : Nat) :
    getDrawResolved (invalidateFbo s) actualDraw = actualDraw := by
  simp [getDrawResolved, invalidateFbo]

theorem known_resolved_query_cached (s : State) (actualDraw : Nat) (h : s.draw ≠ MAX_U32) :
    getDrawResolved s actualDraw = s.draw := by
  simp [getDrawResolved, h]

--ai: a valid cache equals GL; an invalid cache delegates to the queried actual binding.
theorem coherent_resolved_query_actual (s : State) (actualDraw : Nat)
    (h : s.draw = MAX_U32 ∨ s.draw = actualDraw) :
    getDrawResolved s actualDraw = actualDraw := by
  rcases h with h | h
  · simp [getDrawResolved, h]
  · simp [getDrawResolved, h]

def colorInspection (s : State) (actualDraw target : Nat) : State :=
  bindDrawFbo (bindDrawFbo s target) (getDrawResolved s actualDraw)

theorem color_inspection_restores_draw (s : State) (actualDraw target : Nat)
    (h : s.draw = MAX_U32 ∨ s.draw = actualDraw) :
    (colorInspection s actualDraw target).draw = actualDraw := by
  have restored := bindDraw_sets_draw (bindDrawFbo s target) (getDrawResolved s actualDraw)
  simpa [colorInspection, getDraw, coherent_resolved_query_actual s actualDraw h] using restored

theorem color_inspection_preserves_read (s : State) (actualDraw target : Nat) :
    (colorInspection s actualDraw target).read = s.read := by
  have first := bindDraw_preserves_read s target
  have second := bindDraw_preserves_read (bindDrawFbo s target) (getDrawResolved s actualDraw)
  simpa [colorInspection, getRead] using second.trans first

theorem invalidated_raw_snapshot_is_not_actual (s : State) (actualDraw : Nat)
    (h : actualDraw ≠ MAX_U32) : (invalidateFbo s).draw ≠ actualDraw := by
  simpa [invalidateFbo] using Ne.symm h

end GxProofs.RhiFbo
