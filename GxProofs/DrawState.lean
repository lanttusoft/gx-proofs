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
  gX — Draw State Machine Specification

  Models the Begin/End pairing protocol from src/wrappers/drawing.{h,c}.
  Every BeginX call pushes a token onto an implicit stack; every EndX call
  must pop the matching token from the top.  Violations cause GL state leaks
  (depth test left on in 2D, wrong FBO bound, wrong shader program, etc.).

  This is a pure stack machine — no backtracking or error recovery.
  The C code logs warnings on mismatch but continues; the formal model
  captures the ideal protocol that callers MUST follow for correctness.

  Modes (6 of the 7 gX pairs — Begin2D/End2D exists in drawing.h
  but is unmodeled; every modeled pair verified in gX drawing.h:47-84):
    Frame   — gX_Drawing_Begin / End (outermost, one per frame)
    Mode3D  — gX_Drawing_Begin3D / End3D (depth/cull/blend save/restore)
    Texture — gX_Drawing_BeginTexture / EndTexture (FBO bind/unbind)
    Shader  — gX_Drawing_BeginShader / EndShader (custom program)
    Blend   — gX_Drawing_BeginBlend / BeginBlendCustomSeparate + EndBlend
    Scissor — gX_Drawing_BeginScissor / EndScissor (scissor test on/off)

  Theorems proven: 15 (6 structural + 5 balanced + 4 caught)
    - begin_some:                begin always succeeds on any stack
    - endMode_empty_fails_all:   endMode on empty stack always fails
    - begin_endMode_identity:    begin(m) then endMode(m) round-trips
    - endMode_mismatch_fails:    endMode with wrong top mode fails
    - stack_lifo_discipline:     cannot close outer before inner
    - unbalanced_at_frame_end:   leftover modes block frame close
    - balanced_seq_ok:           5 realistic sequences are balanced
    - orphan_end_fails:          End without Begin caught
    - crossed_scopes_fails:      LIFO violation caught
    - missing_end_unbalanced:    leaked scope caught
-/

namespace GxProofs.DrawState

-- Six modes, one per Begin/End pair in drawing.h:47-75
inductive DrawMode : Type where
  | frame   : DrawMode
  | mode3D  : DrawMode
  | texture : DrawMode
  | shader  : DrawMode
  | blend   : DrawMode
  | scissor : DrawMode
deriving DecidableEq, Repr

open DrawMode

-- The implicit stack: empty list = idle (no active scopes)
def DrawStack := List DrawMode

-- ------ Operations ------

-- Begin: push the mode onto the stack.  Always succeeds.
def begin (s : DrawStack) (m : DrawMode) : DrawStack :=
  m :: s

-- End: pop the top of the stack if it matches m.  Returns none on underflow or mismatch.
def endMode (s : DrawStack) (m : DrawMode) : Option DrawStack :=
  match s with
  | []      => none
  | t :: ts => if t = m then some ts else none

--ai: finite sequence witnesses reduce in the kernel, without compiler-trust axioms.
-- (mode, isBegin) — isBegin=true for Begin, false for End
def isBalanced (ops : List (DrawMode × Bool)) : Bool :=
  go [] ops
where
  go (s : DrawStack) (ops : List (DrawMode × Bool)) : Bool :=
    match ops with
    | [] => s.isEmpty
    | (m, true) :: rest  => go (m :: s) rest
    | (m, false) :: rest =>
      match s with
      | [] => false
      | t :: ts => if t == m then go ts rest else false

-- ------ Structural Theorems ------

-- 1. begin always increases stack length by 1
theorem begin_some (s : DrawStack) (m : DrawMode) : (begin s m).length = s.length + 1 := by
  simp [begin]

-- 2. endMode on empty stack fails for any mode
theorem endMode_empty_fails_all : ∀ (m : DrawMode), endMode ([] : DrawStack) m = none := by
  intro m; simp [endMode]

-- 3. begin then endMode of the same mode is identity
theorem begin_endMode_identity (s : DrawStack) (m : DrawMode) :
    endMode (begin s m) m = some s := by
  simp [begin, endMode]

-- 4. endMode with a mismatched top mode fails
theorem endMode_mismatch_fails (s : DrawStack) (m_top m_end : DrawMode) (h : m_top ≠ m_end) :
    endMode (m_top :: s) m_end = none := by
  simp [endMode, h]

-- 5. Stack LIFO discipline: cannot close an outer scope while an inner one is open.
--    If we did: begin outer, begin inner, endMode outer → fails because inner is on top.
theorem stack_lifo_discipline (s : DrawStack) (outer inner : DrawMode) (h : outer ≠ inner) :
    endMode (inner :: outer :: s) outer = none := by
  simp [endMode, h.symm]

-- 6. Unbalanced stack blocks frame close: if the stack is nonempty and the top is NOT Frame,
--    then endMode frame fails (leaked scope prevents proper frame teardown).
theorem unbalanced_at_frame_end (s : DrawStack) (m : DrawMode) (h : m ≠ frame) :
    endMode (m :: s) frame = none := by
  simp [endMode, h]

-- ------ Concrete valid sequences (computation theorems) ------

-- Canvas draw: BeginTexture → BeginBlend → BeginScissor → EndScissor → EndBlend → EndTexture
def canvasDrawSeq : List (DrawMode × Bool) :=
  [(texture, true), (blend, true), (scissor, true), (scissor, false), (blend, false), (texture, false)]

theorem canvasDrawSeq_balanced : isBalanced canvasDrawSeq := by
  unfold isBalanced canvasDrawSeq; decide

-- 3D render-to-texture: BeginTexture → Begin3D → End3D → EndTexture
def rt3DSeq : List (DrawMode × Bool) :=
  [(texture, true), (mode3D, true), (mode3D, false), (texture, false)]

theorem rt3DSeq_balanced : isBalanced rt3DSeq := by
  unfold isBalanced rt3DSeq; decide

-- Shader in texture: BeginTexture → BeginShader → EndShader → EndTexture
def shaderInTextureSeq : List (DrawMode × Bool) :=
  [(texture, true), (shader, true), (shader, false), (texture, false)]

theorem shaderInTextureSeq_balanced : isBalanced shaderInTextureSeq := by
  unfold isBalanced shaderInTextureSeq; decide

-- Nested textures: BeginTexture → BeginTexture → EndTexture → EndTexture
def nestedTextureSeq : List (DrawMode × Bool) :=
  [(texture, true), (texture, true), (texture, false), (texture, false)]

theorem nestedTextureSeq_balanced : isBalanced nestedTextureSeq := by
  unfold isBalanced nestedTextureSeq; decide

-- Full frame: Begin → Texture → 3D → End3D → EndTexture → Texture → Blend → EndBlend → EndTexture → End
def fullFrameSeq : List (DrawMode × Bool) :=
  [(frame, true),
   (texture, true), (mode3D, true), (mode3D, false), (texture, false),
   (texture, true), (blend, true), (blend, false), (texture, false),
   (frame, false)]

theorem fullFrameSeq_balanced : isBalanced fullFrameSeq := by
  unfold isBalanced fullFrameSeq; decide

-- ------ Invalid sequences (caught by proofs) ------

-- Orphan end: End without matching Begin
def orphanEndSeq : List (DrawMode × Bool) :=
  [(mode3D, false)]

theorem orphanEnd_fails : ¬ isBalanced orphanEndSeq := by
  unfold isBalanced orphanEndSeq; decide

-- Crossed scopes: Begin A, Begin B, End A, End B (violates LIFO)
def crossedScopesSeq : List (DrawMode × Bool) :=
  [(texture, true), (shader, true), (texture, false), (shader, false)]

theorem crossedScopes_fails : ¬ isBalanced crossedScopesSeq := by
  unfold isBalanced crossedScopesSeq; decide

-- Missing End: Begin A, Begin B, End B (scope A leaked)
def missingEndSeq : List (DrawMode × Bool) :=
  [(texture, true), (shader, true), (shader, false)]

theorem missingEnd_fails : ¬ isBalanced missingEndSeq := by
  unfold isBalanced missingEndSeq; decide

-- Double Begin with single End (one scope leaked)
def doubleBeginSeq : List (DrawMode × Bool) :=
  [(texture, true), (texture, true), (texture, false)]

theorem doubleBegin_fails : ¬ isBalanced doubleBeginSeq := by
  unfold isBalanced doubleBeginSeq; decide

end GxProofs.DrawState
