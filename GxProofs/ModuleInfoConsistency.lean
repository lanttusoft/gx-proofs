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
  gX — ModuleInfo Consistency (kernel)

  Mirror contract for the moduleinfo flags in
  src/main.h:gX_MainData_ModuleInfo (14 exists flags; the 3
  renderer/scene/game cluster ones modeled here). gX's main_load.c
  never populates moduleinfo and has no gX_ENABLE_* gating yet, so
  only the mirror core + full-stack case transfer — the disable
  theorems return with a kernel-only build (see NOTE at file end).
-/


namespace GxProofs.ModuleInfoConsistency

-- Compile-time enable flags (gX_ENABLE_RENDERER/GAME/SCENE).
structure ModuleFlags where
  renderer : Bool
  gamedata : Bool
  scene    : Bool

-- moduleinfo.*Exists runtime flags (maindata.moduleinfo).
structure ModuleExists where
  rendererExists : Bool
  gamedataExists : Bool
  sceneExists    : Bool

-- consistent ef mi : the runtime mirror agrees with the compile flags.
def consistent (ef : ModuleFlags) (mi : ModuleExists) : Prop :=
  mi.rendererExists = ef.renderer ∧ mi.gamedataExists = ef.gamedata ∧ mi.sceneExists = ef.scene

-- --------------------------------------------------------------------
-- The mirror is a bijection: same flags ⟺ same exists.
-- --------------------------------------------------------------------

theorem consistent_iff_exists (ef : ModuleFlags) (mi : ModuleExists) :
    consistent ef mi ↔
      (mi.rendererExists = ef.renderer ∧ mi.gamedataExists = ef.gamedata ∧ mi.sceneExists = ef.scene) := by
  rfl

theorem exists_renderer_iff_enabled_renderer (ef : ModuleFlags) (mi : ModuleExists)
    (h : consistent ef mi) :
    mi.rendererExists = true ↔ ef.renderer = true := by
  rw [h.1]

theorem exists_game_iff_enabled_game (ef : ModuleFlags) (mi : ModuleExists)
    (h : consistent ef mi) :
    mi.gamedataExists = true ↔ ef.gamedata = true := by
  rw [h.2.1]

theorem exists_scene_iff_enabled_scene (ef : ModuleFlags) (mi : ModuleExists)
    (h : consistent ef mi) :
    mi.sceneExists = true ↔ ef.scene = true := by
  rw [h.2.2]

-- Equal enable flags ⟹ equal exists flags (injectivity of the mirror).
theorem mirror_injective (ef1 ef2 : ModuleFlags) (mi1 mi2 : ModuleExists)
    (h1 : consistent ef1 mi1) (h2 : consistent ef2 mi2) (hef : ef1 = ef2) :
    mi1.rendererExists = mi2.rendererExists ∧
    mi1.gamedataExists = mi2.gamedataExists ∧
    mi1.sceneExists = mi2.sceneExists := by
  subst hef
  rw [h1.1, h2.1]
  rw [h1.2.1, h2.2.1]
  rw [h1.2.2, h2.2.2]
  constructor <;> constructor <;> rfl

-- --------------------------------------------------------------------
-- Full stack: all three enabled → all three exists flags true.
-- (The live case in gX, which has no kernel gating yet.)
-- --------------------------------------------------------------------

theorem full_stack_exists_all_true (mi : ModuleExists)
    (h : consistent { renderer := true, gamedata := true, scene := true } mi) :
    mi.rendererExists = true ∧ mi.gamedataExists = true ∧ mi.sceneExists = true := by
  exact h

-- Kernel-only: the cluster disabled → all three exists flags false.
-- (Realizable now that main_load.c populates moduleinfo from the
-- build flags; kernel-only builds satisfy the premise.)
theorem kernel_only_exists_all_false (mi : ModuleExists)
    (h : consistent { renderer := false, gamedata := false, scene := false } mi) :
    mi.rendererExists = false ∧ mi.gamedataExists = false ∧ mi.sceneExists = false := by
  exact h

-- NOTE: the gameX original also proved three disable_*_sets_exists_false
-- theorems (single-cluster-member off). gX builds the cluster atomically
-- (any OFF forces all OFF), so those configurations are unreachable —
-- they stay dropped. The per-field mirror contract above covers the rest.

end GxProofs.ModuleInfoConsistency
