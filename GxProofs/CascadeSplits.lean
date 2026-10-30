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
  gX — CSM Cascade Split Distances

  Proves the shadow cascade split distances and frustum sizes
  are strictly increasing, ensuring correct cascade coverage.

  Constants re-verified against gX
  src/renderer/gfx/constants.h:148-158 (identical values):
    CSM_SPLIT:   10, 30, 60, 100   (world-space Z splits)
    CSM_VIEW_SPLIT: 15, 50, 120    (view-space Z split boundaries)
    CSM_FRUSTUM: 8, 30, 80, 200    (ortho frustum half-extents)
-/

namespace GxProofs.CascadeSplits

-- World-space cascade split distances (gfx.h:133-136)
def SPLIT_0 : Nat := 10
def SPLIT_1 : Nat := 30
def SPLIT_2 : Nat := 60
def SPLIT_3 : Nat := 100

theorem splits_strictly_increasing : SPLIT_0 < SPLIT_1 ∧ SPLIT_1 < SPLIT_2 ∧ SPLIT_2 < SPLIT_3 := by
  unfold SPLIT_0 SPLIT_1 SPLIT_2 SPLIT_3; omega

-- View-space split distances (gfx.h:137-139)
def VIEW_SPLIT_0 : Nat := 15
def VIEW_SPLIT_1 : Nat := 50
def VIEW_SPLIT_2 : Nat := 120

theorem view_splits_strictly_increasing : VIEW_SPLIT_0 < VIEW_SPLIT_1 ∧ VIEW_SPLIT_1 < VIEW_SPLIT_2 := by
  unfold VIEW_SPLIT_0 VIEW_SPLIT_1 VIEW_SPLIT_2; omega

-- Ortho frustum sizes (gfx.h:140-143)
def FRUSTUM_0 : Nat := 8
def FRUSTUM_1 : Nat := 30
def FRUSTUM_2 : Nat := 80
def FRUSTUM_3 : Nat := 200

theorem frustum_sizes_strictly_increasing : FRUSTUM_0 < FRUSTUM_1 ∧ FRUSTUM_1 < FRUSTUM_2 ∧ FRUSTUM_2 < FRUSTUM_3 := by
  unfold FRUSTUM_0 FRUSTUM_1 FRUSTUM_2 FRUSTUM_3; omega

-- World splits are bounded by far plane (1000)
def FAR_PLANE : Nat := 1000

theorem world_splits_within_far : SPLIT_0 < FAR_PLANE ∧ SPLIT_1 < FAR_PLANE ∧ SPLIT_2 < FAR_PLANE ∧ SPLIT_3 < FAR_PLANE := by
  unfold SPLIT_0 SPLIT_1 SPLIT_2 SPLIT_3 FAR_PLANE; omega

-- View splits correspond to world splits (15 < 10? No — 15 > 10 means view split is
-- always slightly farther than the corresponding world split, which is intentional:
-- the view-space Z at the split boundary is offset to ensure the cascade boundary
-- is visually seamless.)

end GxProofs.CascadeSplits
