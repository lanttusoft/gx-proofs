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
  //ai: postprocess denominator and empty-chain contracts, grounded in
  src/renderer/postprocess.c and shader/postprocess/blur_gauss.frag.
  Historical counterexamples are retained; repaired passes use matching native
  extents and a separate presentation. GPU/float/GL assumptions remain external.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace GxProofsGfx.PostprocessContracts

def uv (fragment extent : ℚ) : ℚ := fragment / extent

theorem matching_extent_identity (extent position : ℚ) (he : extent ≠ 0) :
    uv (extent * position) extent = position := by
  unfold uv
  field_simp

theorem matching_extent_range (fragment extent : ℚ) (he : 0 < extent)
    (hf : 0 ≤ fragment) (hu : fragment ≤ extent) :
    0 ≤ uv fragment extent ∧ uv fragment extent ≤ 1 := by
  unfold uv
  constructor
  · exact div_nonneg hf (le_of_lt he)
  · rw [div_le_iff₀ he]
    simpa using hu

theorem denominator_ratio (target source position : ℚ) :
    uv (target * position) source = (target / source) * position := by
  unfold uv
  ring

theorem coordinate_error (target source position : ℚ) (ht : target ≠ 0) :
    uv (target * position) source - uv (target * position) target =
      (target / source - 1) * position := by
  rw [denominator_ratio, matching_extent_identity target position ht]
  ring

theorem half_resolution_doubles (source position : ℚ) (hs : source ≠ 0) :
    uv ((2 * source) * position) source = 2 * position := by
  unfold uv
  field_simp

theorem half_resolution_leaves_unit_interval (source position : ℚ)
    (hs : source ≠ 0) (hp : 1/2 < position) :
    1 < uv ((2 * source) * position) source := by
  rw [half_resolution_doubles source position hs]
  linarith

--ai: under repeat semantics, supplied tile subtraction gives identical lookups.
def repeatTile (coordinate : ℚ) (tile : ℤ) : ℚ := coordinate - tile

theorem repeat_tile_shift (coordinate : ℚ) (tile : ℤ) :
    repeatTile (coordinate + 1) (tile + 1) = repeatTile coordinate tile := by
  simp only [repeatTile, Int.cast_add, Int.cast_one]
  ring

theorem half_resolution_two_tile_witness :
    repeatTile (uv (2048 * (1/4)) 1024) 0 =
      repeatTile (uv (2048 * (3/4)) 1024) 1 := by
  norm_num [repeatTile, uv]

theorem half_resolution_not_identity :
    uv (2048 * (3/4)) 1024 ≠ uv (2048 * (3/4)) 2048 := by
  norm_num [uv]

theorem asymmetric_y_mismatch : uv 864 576 = 3/2 ∧ uv 864 1152 = 3/4 := by
  norm_num [uv]

--ai: source texel offsets and target-normalized base coordinates are different roles.
def texelStep (source : ℚ) : ℚ := 1 / source

theorem source_texel_offset (fragment target source offset : ℚ) :
    uv fragment target + offset * texelStep source =
      fragment / target + offset / source := by
  unfold uv texelStep
  ring

theorem source_target_steps_distinct : texelStep 1024 ≠ texelStep 2048 := by
  norm_num [texelStep]

--ai: only the explicitly enabled opaque canvas contribution is modeled here;
-- feedback and other inject slots are disabled, and texture transfer is ideal.
def assembleStart (injectCanvas : Bool) (canvas : ℚ) : ℚ :=
  if injectCanvas then canvas else 0

def applyChain (effects : List (ℚ → ℚ)) (input : ℚ) : ℚ :=
  effects.foldl (fun value effect => effect value) input

theorem empty_chain_preserves_start (start : ℚ) : applyChain [] start = start := by
  rfl

theorem empty_chain_canvas_identity (canvas : ℚ) :
    applyChain [] (assembleStart true canvas) = canvas := by
  rfl

theorem empty_chain_without_injection_black (canvas : ℚ) :
    applyChain [] (assembleStart false canvas) = 0 := by
  rfl

theorem empty_chain_not_unconditional_scene_identity :
    applyChain [] (assembleStart false 1) ≠ (1 : ℚ) := by
  norm_num [applyChain, assembleStart]

theorem identity_effect_preserves_start (start : ℚ) :
    applyChain [id] start = start := by
  rfl

--ai: historical +1 Nat finality models executed nonoverflowing indices, not raw unsigned
-- subtraction at loops=0; a zero-loop slot never executes a production pass.
-- Production finality depends on authored last slot, not last nonempty slot.
def finalPass (slot amount iteration loops : ℕ) : Prop :=
  slot + 1 = amount ∧ iteration + 1 = loops

theorem zero_loop_slot_never_final (slot amount iteration : ℕ) :
    ¬ finalPass slot amount iteration 0 := by
  simp [finalPass]

theorem preceding_slot_not_final (slot amount iteration loops : ℕ)
    (h : slot + 1 < amount) : ¬ finalPass slot amount iteration loops := by
  unfold finalPass
  omega

theorem trailing_zero_loop_counterexample (iteration : ℕ) :
    ¬ finalPass 0 2 iteration 4 ∧ ¬ finalPass 1 2 iteration 0 := by
  constructor
  · norm_num [finalPass]
  · exact zero_loop_slot_never_final 1 2 iteration

--ai: repaired C routing selects ping/pong by completed-pass count and presents afterward.
-- 0=start, 1=ping, 2=pong; actual backing names must be distinct and loaded.
def currentSource (completed : ℕ) : ℕ :=
  if completed = 0 then 0 else if completed % 2 = 0 then 2 else 1

def nextTarget (completed : ℕ) : ℕ := if completed % 2 = 0 then 1 else 2

theorem next_pass_does_not_alias_source (completed : ℕ) :
    currentSource completed ≠ nextTarget completed := by
  by_cases h : completed = 0
  · simp [currentSource, nextTarget, h]
  · by_cases hm : completed % 2 = 0 <;> simp [currentSource, nextTarget, h, hm]

theorem committed_source_is_written_target (completed : ℕ) :
    currentSource (completed + 1) = nextTarget completed := by
  by_cases hm : completed % 2 = 0
  · have hnext : (completed + 1) % 2 ≠ 0 := by omega
    simp [currentSource, nextTarget, hm, hnext]
  · have hnext : (completed + 1) % 2 = 0 := by omega
    simp [currentSource, nextTarget, hm, hnext]

def passCount (loops : List ℕ) : ℕ := loops.sum
def presentedSource (loops : List ℕ) : ℕ := currentSource (passCount loops)

theorem zero_tail_preserves_executed_count (loops : List ℕ) :
    passCount (loops ++ [0]) = passCount loops := by simp [passCount]

theorem zero_tail_preserves_presentation (loops : List ℕ) :
    presentedSource (loops ++ [0]) = presentedSource loops := by
  simp [presentedSource, passCount]

theorem empty_count_presents_start : presentedSource [] = 0 := by
  simp [presentedSource, passCount, currentSource]

theorem all_zero_slots_present_start (count : ℕ) :
    presentedSource (List.replicate count 0) = 0 := by
  simp [presentedSource, passCount, currentSource]

theorem repaired_zero_tail_witness : presentedSource [1, 0] = 1 := by
  norm_num [presentedSource, passCount, currentSource]

--ai: opaque scene assembly has a default canvas when no auxiliary source is enabled.
def usesCanvas (explicitCanvas inject feedback : Bool) : Bool :=
  explicitCanvas || (!inject && !feedback)

theorem unconfigured_input_uses_scene (explicitCanvas : Bool) :
    usesCanvas explicitCanvas false false = true := by
  cases explicitCanvas <;> decide

theorem default_opaque_assembly_preserves_scene (explicitCanvas : Bool) (canvas : ℚ) :
    assembleStart (usesCanvas explicitCanvas false false) canvas = canvas := by
  rw [unconfigured_input_uses_scene]
  rfl

theorem explicit_canvas_retained (inject feedback : Bool) :
    usesCanvas true inject feedback = true := by simp [usesCanvas]

theorem auxiliary_input_does_not_force_canvas (inject feedback : Bool)
    (h : inject = true ∨ feedback = true) : usesCanvas false inject feedback = false := by
  cases inject <;> cases feedback <;> simp_all [usesCanvas]

def bypass (hasPass explicitCanvas inject feedback : Bool) : Bool :=
  !hasPass && !inject && !feedback && !explicitCanvas

theorem unconfigured_empty_bypasses : bypass false false false false = true := by decide

theorem configured_layer_not_bypassed (hasPass explicitCanvas inject feedback : Bool)
    (h : explicitCanvas = true ∨ inject = true ∨ feedback = true) :
    bypass hasPass explicitCanvas inject feedback = false := by
  cases hasPass <;> cases explicitCanvas <;> cases inject <;> cases feedback <;>
    simp_all [bypass]

end GxProofsGfx.PostprocessContracts
