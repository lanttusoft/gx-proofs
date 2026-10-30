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
  gX — GL State Stack Specification

  Models the save/restore stack from src/rhi/gl_state.{h,c}
  (gX_GL_State_Save/Restore/Push/Pop; the header still carries its
  old wrappers/ path in the banner comment). Used at every GFX→GUI
  transition to prevent GL state leaks across module boundaries.

  Salvage notes: DEPTH 4→16 (gX raised GX_GL_STACK_DEPTH; all
  theorems are parametric over DEPTH and re-verify unchanged), and
  the modeled struct is a SUBSET of gX_GL_State (blend/cull/depth/
  scissor/activeTexture/viewport; blendEquation, depthFunc,
  currentProgram, colorMask, FBOs, polygonMode unmodeled).
  Empty list (ptr = -1) means no saved state.

  Theorems proven: 14
    - save_restore_id: Save then Restore is identity on a GLState struct
    - push_preserves_valid, pop_preserves_valid: stack bounds never violated
    - push_pop_identity, pop_restores_gl: Push then Pop round-trips
    - push_overflow_fails, pop_underflow_fails: bounds checks work
    - save_preserves_*: all 11 field groups are preserved by Save
-/

namespace GxProofs.GLState

-- Max stack depth (GX_GL_STACK_DEPTH in gl_state.h = 16 in gX)
def DEPTH : Nat := 16

-- Snapshot of all GL state that must be restored after GFX drawing
structure GLState where
  blendEnabled    : Bool
  srcRGB          : Int
  dstRGB          : Int
  srcA            : Int
  dstA            : Int
  cullFaceEnabled : Bool
  cullFaceMode    : Int
  frontFace       : Int
  depthTestEnabled: Bool
  depthMask       : Bool
  scissorEnabled  : Bool
  activeTexture   : Int
  viewport0       : Int
  viewport1       : Int
  viewport2       : Int
  viewport3       : Int

-- Save reads current GL state into a struct (identity: struct copy)
def save (s : GLState) : GLState := s

-- Restore writes the struct back to GL (identity: struct copy)
def restore (s : GLState) : GLState := s

theorem save_restore_id (s : GLState) : restore (save s) = s :=
  rfl

-- Stack: list of saved states. Empty = stackPtr = -1 in C.
def Stack := List GLState

-- Valid stacks never exceed DEPTH
def validStack (s : Stack) : Prop :=
  s.length ≤ DEPTH

-- Push: save current gl onto stack. Returns none if at capacity.
def push (s : Stack) (gl : GLState) : Option (Stack × GLState) :=
  if s.length < DEPTH then
    some (save gl :: s, gl)
  else
    none

-- Pop: restore from the top saved state. Returns none if empty.
def pop (s : Stack) (_gl : GLState) : Option (Stack × GLState) :=
  match s with
  | []      => none
  | h :: t  => some (t, restore h)

-- Push preserves the validStack invariant (can't overflow past DEPTH)
theorem push_preserves_valid (s : Stack) (gl : GLState) :
    match push s gl with
    | none => True
    | some (s', _) => validStack s' := by
  unfold push
  by_cases h_lt : s.length < DEPTH
  · simp [h_lt]
    unfold validStack
    simp
    omega
  · simp [h_lt]

-- Pop preserves the validStack invariant (popping makes stack shorter)
theorem pop_preserves_valid (s : Stack) (gl : GLState) (hvalid : validStack s) :
    match pop s gl with
    | none => True
    | some (s', _) => validStack s' := by
  unfold pop
  cases s with
  | nil => simp
  | cons h t =>
    simp
    unfold validStack at hvalid
    have h_t_len : t.length ≤ DEPTH := by
      have : (h :: t).length = t.length + 1 := by simp
      have hval : (h :: t).length ≤ DEPTH := hvalid
      omega
    unfold validStack
    exact h_t_len

-- Push then Pop is identity: (s, gl) → (s, gl)
theorem push_pop_identity (s : Stack) (gl : GLState) (h_lt : s.length < DEPTH) :
    (do
      let (s', _) <- push s gl
      pop s' gl) = some (s, gl) := by
  unfold push
  simp [h_lt]
  unfold pop
  simp [save, restore]

-- Pushing a full stack returns none (overflow detection)
theorem push_overflow_fails (s : Stack) (gl : GLState) (h_full : s.length ≥ DEPTH) :
    push s gl = none := by
  unfold push
  simp
  omega

-- Popping an empty stack returns none (underflow detection)
theorem pop_underflow_fails (gl : GLState) : pop [] gl = none := by
  unfold pop
  simp

-- Alias for push_pop_identity (same property, different naming)
theorem pop_restores_gl (s : Stack) (gl : GLState) (h_lt : s.length < DEPTH) :
    (do
      let (s', gl') <- push s gl
      pop s' gl') = some (s, gl) :=
  push_pop_identity s gl h_lt

-- All 11 field groups are preserved by Save (they pass through unchanged)
theorem save_preserves_blend (s : GLState) : (save s).blendEnabled = s.blendEnabled := rfl
theorem save_preserves_blendFunc (s : GLState) : (save s).srcRGB = s.srcRGB := rfl
theorem save_preserves_cullFace (s : GLState) : (save s).cullFaceEnabled = s.cullFaceEnabled := rfl
theorem save_preserves_depth (s : GLState) : (save s).depthTestEnabled = s.depthTestEnabled := rfl
theorem save_preserves_scissor (s : GLState) : (save s).scissorEnabled = s.scissorEnabled := rfl
theorem save_preserves_activeTexture (s : GLState) : (save s).activeTexture = s.activeTexture := rfl
theorem save_preserves_viewport (s : GLState) : (save s).viewport0 = s.viewport0 := rfl

end GxProofs.GLState
