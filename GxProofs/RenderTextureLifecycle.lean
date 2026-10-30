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
  gX — Render Texture Loading State Machine

  Models the lifecycle of gX_RendererGFX_RenderTexture
  (src/renderer/gfx/texture.c: loadAsap set on init,
  load guard loadAsap && backendLoaded && !loaded). The C guard
  includes backendLoaded (engine readiness), unmodeled here —
  canLoad is the asset-side readiness half.

  State transitions:
    init → loadAsap=true, loaded=false, reload=false
    load → loaded=true, loadAsap=false
    unload → loaded=false
    markReload → reload=true
    reload → unload + load → loaded=true, reload=false

  Invariants:
    - Load can only happen when !loaded && loadAsap
    - Unload can only happen when loaded
    - Reload requires loaded && reload
    - Double-load is prevented by the !loaded check
    - Double-unload is prevented by the loaded check
-/

namespace GxProofs.RenderTextureLifecycle

-- Loading state
structure LoadingState where
  loadAsap : Bool
  loaded   : Bool
  reload   : Bool

def initialState : LoadingState :=
  { loadAsap := true, loaded := false, reload := false }

-- Valid transitions
def canLoad (s : LoadingState) : Prop :=
  s.loadAsap ∧ ¬s.loaded

def canUnload (s : LoadingState) : Prop :=
  s.loaded

def canReload (s : LoadingState) : Prop :=
  s.loaded ∧ s.reload

-- Transition: load
def load (s : LoadingState) : LoadingState :=
  { s with loadAsap := false, loaded := true }

-- Transition: unload
def unload (s : LoadingState) : LoadingState :=
  { s with loaded := false }

-- Transition: mark for reload
def markReload (s : LoadingState) : LoadingState :=
  { s with reload := true }

-- Transition: execute reload (clears reload flag)
def doReload (s : LoadingState) : LoadingState :=
  { load (unload s) with reload := false }

-- Theorems

-- Init produces the initial state
theorem init_state_correct : initialState.loadAsap ∧ ¬initialState.loaded ∧ ¬initialState.reload := by
  unfold initialState; simp

-- Load requires loadAsap && !loaded
theorem load_requires_ready (s : LoadingState) (h : canLoad s) : s.loadAsap ∧ ¬s.loaded := h

-- Load sets loaded=true, loadAsap=false
theorem load_effect (s : LoadingState) (_h : canLoad s) : (load s).loaded ∧ ¬(load s).loadAsap := by
  unfold load; simp

-- Unload requires loaded
theorem unload_requires_loaded (s : LoadingState) (h : canUnload s) : s.loaded := h

-- Unload sets loaded=false
theorem unload_effect (s : LoadingState) (_h : canUnload s) : ¬(unload s).loaded := by
  unfold unload; simp

-- Cannot load twice without unload
theorem no_double_load (s : LoadingState) (_h : canLoad s) : ¬canLoad (load s) := by
  unfold canLoad load; simp

-- Cannot unload twice without load
theorem no_double_unload (s : LoadingState) (_h : canUnload s) : ¬canUnload (unload s) := by
  unfold canUnload unload; simp

-- Load then unload returns to unloaded state
theorem load_then_unload (s : LoadingState) (_h : canLoad s) : ¬(unload (load s)).loaded := by
  unfold unload load; simp

-- Reload cycle: markReload then doReload returns to loaded state
theorem reload_cycle (s : LoadingState) (_h_loaded : s.loaded) (_h_reload : s.reload) : (doReload s).loaded := by
  unfold doReload load unload; simp

-- Reload clears the reload flag
theorem reload_clears_flag (s : LoadingState) (_h_loaded : s.loaded) (_h_reload : s.reload) : ¬(doReload s).reload := by
  unfold doReload load unload; simp

end GxProofs.RenderTextureLifecycle
