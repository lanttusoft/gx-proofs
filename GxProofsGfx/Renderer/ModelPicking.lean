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
  gX — Nearest Mesh-Hit Picking Contract

  Models the candidate selection in src/renderer/gfx/scene.c:
  gX_RendererGFX_Model_Pick accepts successful mesh ray collisions below its
  999999 distance sentinel and keeps a candidate only when its distance is
  strictly less than the current best. Misses are represented by none; hits
  retain their model heap index and ray distance.

  This proves the selection contract over collision results. The runtime picker
  check remains responsible for ray construction, model transforms, mesh
  intersection, viewport mapping, and ImGui mouse capture.

  Theorems proven:
    - nearest_hit_spec:             a selected result is an input hit and no
                                    farther than any eligible hit
    - pick_nearest_spec:            the collision-result picker satisfies the
                                    same nearest-hit contract
    - no_eligible_hit_returns_none: empty eligible input has no selection
    - misses_are_neutral:           adding a mesh miss does not change selection
    - out_of_range_is_neutral:      hits beyond the C sentinel are ignored
    - closer_hit_replaces:          a strictly closer hit replaces the best
    - farther_hit_keeps_best:       a farther hit cannot replace the best
    - equal_distance_keeps_first:   strict comparison preserves traversal order
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxProofsGfx.ModelPicking

noncomputable section

open Classical

--opencode: successful mesh intersections carry the selected model heap index.
structure RayHit where
  modelIndex : Nat
  distance : ℝ

--opencode: preserve the renderer's finite closest-distance sentinel.
def pickDistanceLimit : ℝ := 999999

--opencode: none represents rc.hit == false; the range gate mirrors scene.c.
def eligibleHits (collisions : List (Option RayHit)) : List RayHit :=
  ((collisions.filterMap id).filter fun hit => hit.distance < pickDistanceLimit)

--opencode: strict less-than mirrors rc.distance < closestDist and retains ties.
def consider (best : Option RayHit) (candidate : RayHit) : Option RayHit :=
  match best with
  | none => some candidate
  | some current =>
      if candidate.distance < current.distance then some candidate else best

--opencode: fold the eligible candidates in the same order as heap traversal.
def nearestHit (hits : List RayHit) : Option RayHit :=
  hits.foldl consider none

--opencode: filter collision misses/range rejects before nearest selection.
def pickNearest (collisions : List (Option RayHit)) : Option RayHit :=
  nearestHit (eligibleHits collisions)

--opencode: a selected result is an input hit and no farther than its peers.
def IsNearest (hits : List RayHit) (best : Option RayHit) : Prop :=
  match best with
  | none => hits = []
  | some selected =>
      selected ∈ hits ∧ ∀ candidate ∈ hits, selected.distance ≤ candidate.distance

--opencode: adding one collision preserves the invariant that best is nearest.
theorem consider_preserves_nearest
    (seen : List RayHit) (best : Option RayHit) (candidate : RayHit)
    (hBest : IsNearest seen best) :
    IsNearest (seen ++ [candidate]) (consider best candidate) := by
  cases best with
  | none =>
      have hSeen : seen = [] := hBest
      subst seen
      simp [IsNearest, consider]
  | some incumbent =>
      rcases hBest with ⟨hMember, hMinimum⟩
      by_cases hCloser : candidate.distance < incumbent.distance
      · simp [IsNearest, consider, hCloser]
        intro other hOther
        rcases hOther with hSeen | hCandidate
        · exact le_trans (le_of_lt hCloser) (hMinimum other hSeen)
        · subst other
          exact le_rfl
      · have hIncumbent : incumbent.distance ≤ candidate.distance :=
          le_of_not_gt hCloser
        simp [IsNearest, consider, hCloser]
        constructor
        · exact Or.inl hMember
        · intro other hOther
          rcases hOther with hSeen | hCandidate
          · exact hMinimum other hSeen
          · subst other
            exact hIncumbent

--opencode: the traversal fold always retains a minimum of the processed hits.
theorem fold_preserves_nearest
    (seen pending : List RayHit) (best : Option RayHit)
    (hBest : IsNearest seen best) :
    IsNearest (seen ++ pending) (pending.foldl consider best) := by
  induction pending generalizing seen best with
  | nil =>
      simpa using hBest
  | cons candidate rest ih =>
      have hStep := consider_preserves_nearest seen best candidate hBest
      have hTail := ih (seen ++ [candidate]) (consider best candidate) hStep
      simpa [List.foldl_cons, List.append_assoc] using hTail

--opencode: state the candidate-membership and minimum-distance contract.
theorem nearest_hit_spec (hits : List RayHit) : IsNearest hits (nearestHit hits) := by
  unfold nearestHit
  exact fold_preserves_nearest [] hits none (by simp [IsNearest])

--opencode: lift the nearest-hit contract to the renderer's collision results.
theorem pick_nearest_spec (collisions : List (Option RayHit)) :
    IsNearest (eligibleHits collisions) (pickNearest collisions) := by
  exact nearest_hit_spec (eligibleHits collisions)

--opencode: prove the picker returns no model when no eligible hit exists.
theorem no_eligible_hit_returns_none (collisions : List (Option RayHit))
    (hEmpty : eligibleHits collisions = []) : pickNearest collisions = none := by
  cases hPick : pickNearest collisions with
  | none => rfl
  | some selected =>
      have hSpec := pick_nearest_spec collisions
      rw [hPick, hEmpty] at hSpec
      simp [IsNearest] at hSpec

--opencode: a miss entry cannot change the selected model or distance.
theorem misses_are_neutral (collisions : List (Option RayHit)) :
    pickNearest (collisions ++ [none]) = pickNearest collisions := by
  simp [pickNearest, eligibleHits, nearestHit, List.filterMap_append]

--opencode: collision distances beyond closestDist's initial sentinel are ignored.
theorem out_of_range_is_neutral
    (collisions : List (Option RayHit)) (hit : RayHit)
    (hFar : pickDistanceLimit ≤ hit.distance) :
    pickNearest (collisions ++ [some hit]) = pickNearest collisions := by
  have hNot : ¬ hit.distance < pickDistanceLimit := not_lt.mpr hFar
  have hRejected : decide (hit.distance < pickDistanceLimit) = false :=
    decide_eq_false hNot
  have hRejectedConst : decide (hit.distance < 999999) = false := by
    simpa [pickDistanceLimit] using hRejected
  have hEligible : eligibleHits (collisions ++ [some hit]) = eligibleHits collisions := by
    simp [eligibleHits, List.filterMap_append, List.filter_append,
      pickDistanceLimit, hRejectedConst]
  change nearestHit (eligibleHits (collisions ++ [some hit])) =
    nearestHit (eligibleHits collisions)
  rw [hEligible]

--opencode: the production strict comparison replaces an incumbent when nearer.
theorem closer_hit_replaces (incumbent candidate : RayHit)
    (hCloser : candidate.distance < incumbent.distance) :
    consider (some incumbent) candidate = some candidate := by
  simp [consider, hCloser]

--opencode: a farther candidate cannot cancel the current nearest result.
theorem farther_hit_keeps_best (incumbent candidate : RayHit)
    (hFarther : incumbent.distance ≤ candidate.distance) :
    consider (some incumbent) candidate = some incumbent := by
  simp [consider, not_lt.mpr hFarther]

--opencode: strict comparison leaves the earlier heap traversal hit on ties.
theorem equal_distance_keeps_first (first second : RayHit)
    (hEqual : first.distance = second.distance) :
    consider (some first) second = some first := by
  simp [consider, hEqual]

end

end GxProofsGfx.ModelPicking
