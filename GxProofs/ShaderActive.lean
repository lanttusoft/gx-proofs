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
  gX — Shader Active Protocol Specification

  Models the invariant from src/wrappers/shader.c and AGENTS.md:
  rlEnableShader(shader.id) / rlSetShader(shader.id, locs) MUST be called
  BEFORE any gX_Shader_SetValue* call.  Uniform uploads silently target the
  previously-active program if the shader is not activated first — this was
  the root cause of invisible models in earlier development sessions.

  Ghost state model: a single Option Nat representing the currently active
  shader program ID.  none = default program (no custom shader bound).
  some id = custom shader #id is active.

  gX is raylib-only: the backend relies on rlgl.State.currentShaderId,
  so the activate-before-upload convention modeled here is the live
  path (the gameX original also discussed a GLFW glUseProgram path
  that does not exist in gX).

  Theorems proven: 10
    - upload_without_shader_fails:    SetValue* on inactive shader fails
    - bindTexture_without_shader_fails: texture bind on inactive shader fails
    - uploadMatrix_without_shader_fails: matrix upload on inactive shader fails
    - use_then_upload_succeeds:       useProgram(id) then upload succeeds
    - use_then_texture_succeeds:      useProgram(id) then bindTexture succeeds
    - use_then_matrix_succeeds:       useProgram(id) then uploadMatrix succeeds
    - endProgram_clears:              endProgram resets to none
    - upload_preserves_active:        successful upload keeps shader active
    - sequence_properties:            combined end-to-end scenarios
-/

--ai: finite shader protocol examples are checked by kernel reduction.
namespace GxProofs.ShaderActive

-- Ghost state: the currently active shader program.
-- none = default shader (no custom program bound).
def ProgramState := Option Nat

-- ------ Operations (all take state → return new state) ------

-- Activate a shader program.
def useProgram (_s : ProgramState) (id : Nat) : ProgramState :=
  some id

-- Deactivate the current shader (restore default).
def endProgram (_s : ProgramState) : ProgramState :=
  none

-- Upload a uniform value.  Fails (returns none) if no shader is active.
def uploadUniform (s : ProgramState) : Option ProgramState :=
  match s with
  | none   => none
  | some _ => some s

-- Bind a texture uniform.  Fails if no shader is active.
def bindTexture (s : ProgramState) : Option ProgramState :=
  match s with
  | none   => none
  | some _ => some s

-- Upload a matrix uniform.  Fails if no shader is active.
def uploadMatrix (s : ProgramState) : Option ProgramState :=
  match s with
  | none   => none
  | some _ => some s

-- ------ Theorems ------

-- 1. Uploading a uniform without an active shader fails.
theorem upload_without_shader_fails : uploadUniform none = none := by
  simp [uploadUniform]

-- 2. Binding a texture without an active shader fails.
theorem bindTexture_without_shader_fails : bindTexture none = none := by
  simp [bindTexture]

-- 3. Uploading a matrix without an active shader fails.
theorem uploadMatrix_without_shader_fails : uploadMatrix none = none := by
  simp [uploadMatrix]

-- 4. Activating a shader then uploading a uniform succeeds.
theorem use_then_upload_succeeds (id : Nat) :
    uploadUniform (useProgram none id) = some (some id) := by
  simp [uploadUniform, useProgram]

-- 5. Activating a shader then binding a texture succeeds.
theorem use_then_texture_succeeds (id : Nat) :
    bindTexture (useProgram none id) = some (some id) := by
  simp [bindTexture, useProgram]

-- 6. Activating a shader then uploading a matrix succeeds.
theorem use_then_matrix_succeeds (id : Nat) :
    uploadMatrix (useProgram none id) = some (some id) := by
  simp [uploadMatrix, useProgram]

-- 7. EndProgram resets the state to none regardless of current program.
theorem endProgram_clears (id : Nat) : endProgram (some id) = none := by
  simp [endProgram]

-- Also clears from any state:
theorem endProgram_clears_all : ∀ (s : ProgramState), endProgram s = none := by
  intro s; simp [endProgram]

-- 8. Successful upload preserves the active shader state.
theorem upload_preserves_active (id : Nat) :
    uploadUniform (some id) = some (some id) := by
  simp [uploadUniform]

-- 9. Combined sequence properties.
theorem sequence_properties :
    -- (a) use → upload → upload → upload works (multiple uniforms)
    (do
      let s1 := useProgram none 1
      let s2 ← uploadUniform s1
      let s3 ← uploadUniform s2
      uploadUniform s3) = some (some 1)
    ∧ -- (b) use → end → upload fails
    (do
      let s1 := useProgram none 1
      let s2 := endProgram s1
      uploadUniform s2) = none
    ∧ -- (c) upload → upload on active shader works
    (do
      let s1 := useProgram none 1
      let s2 ← uploadUniform s1
      bindTexture s2) = some (some 1)
    := by
  decide

end GxProofs.ShaderActive
