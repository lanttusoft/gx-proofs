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
  //ai: bounded light-heap and shared point-shadow-array lifecycle model.

  Models two heap slots, matching the light-hole/reuse runtime fixture, and a
  shared point-shadow storage state in src/renderer/gfx/light.c and
  shader.c. The lazy shader scan requests full storage iff either modeled live
  slot is a shadow-casting non-sun light; unused slots, suns and non-casters do
  not request it. The source guard also checks that indices outside the
  64-slot shadow domain do not demand or attach this storage. Removal makes the
  slot logically unused and detaches its borrowed
  array reference without destroying renderer-owned storage. Add reuses the
  first hole and initializes a clean, non-shadowing light. Updating a live
  shadow-casting point light promotes absent/placeholder storage to the shared
  array and attaches the slot. Shader span remains heap-indexed across holes.

  Separately, the layer arithmetic covers the declared 64-slot, six-face
  capacity: valid slot/face pairs map injectively into 384 layers, so distinct
  valid lights and distinct faces cannot alias. The light heap permits 128
  slots, so draw.c skips point-shadow passes for indices at or above 64 rather
  than attaching an out-of-range layer or aliasing slot 63. The source guard
  pins the heap configuration and growth limit; Lean models the finite capacity
  arithmetic and checked-layer policy, not execution of the C heap.

  Failed allocation from either absent or placeholder storage leaves the common
  state absent and retryable. Renderer teardown also resets shared storage to
  absent. These are control-flow contracts, not claims that GPU allocation
  succeeds or fails.

  Array allocation success is assumed by the update transition. The model does
  not prove GPU allocation, depth rendering, sampling quality, C control flow
  beyond source-guarded contracts, or concurrent renderer updates. Runtime
  light-hole/reuse and point-shadow image checks remain independent evidence.
-/

namespace GxProofs.GfxLightShadowSlots

inductive SlotIndex where
  | zero
  | one
  deriving DecidableEq, Repr

inductive Storage where
  | absent
  | placeholder
  | pointShadowArray
  deriving DecidableEq, Repr

structure LightSlot where
  used : Bool
  castsShadows : Bool
  sun : Bool
  shadowReference : Bool
  deriving DecidableEq, Repr

structure State where
  storage : Storage
  slot0 : LightSlot
  slot1 : LightSlot
  deriving DecidableEq, Repr

def emptySlot : LightSlot := ⟨false, false, false, false⟩
def freshLight : LightSlot := ⟨true, false, false, false⟩

def emptyState : State := ⟨.absent, emptySlot, emptySlot⟩

def getSlot (state : State) (index : SlotIndex) : LightSlot :=
  match index with
  | .zero => state.slot0
  | .one => state.slot1

def setSlot (state : State) (index : SlotIndex) (light : LightSlot) : State :=
  match index with
  | .zero => { state with slot0 := light }
  | .one => { state with slot1 := light }

def addFirstEmpty (state : State) : State × Option SlotIndex :=
  if !state.slot0.used then (setSlot state .zero freshLight, some .zero)
  else if !state.slot1.used then (setSlot state .one freshLight, some .one)
  else (state, none)

def detach (light : LightSlot) : LightSlot :=
  { light with used := false, shadowReference := false }

def removeLight (state : State) (index : SlotIndex) : State :=
  setSlot state index (detach (getSlot state index))

def removeAll (state : State) : State :=
  { state with slot0 := detach state.slot0, slot1 := detach state.slot1 }

def ensurePlaceholder (state : State) : State :=
  if state.storage = .absent then { state with storage := .placeholder }
  else state

def pointShadowDemand (light : LightSlot) : Bool :=
  light.used && light.castsShadows && !light.sun

def stateNeedsPointShadowArray (state : State) : Bool :=
  pointShadowDemand state.slot0 || pointShadowDemand state.slot1

def initializeSharedArray (storage : Storage) (allocationSucceeds : Bool) : Storage :=
  match storage with
  | .absent => if allocationSucceeds then .pointShadowArray else .absent
  | .placeholder => if allocationSucceeds then .pointShadowArray else .absent
  | .pointShadowArray => .pointShadowArray

def initializeLazyStorage (state : State) (allocationSucceeds : Bool) : State :=
  if state.storage = .absent then
    if stateNeedsPointShadowArray state then
      { state with storage := initializeSharedArray .absent allocationSucceeds }
    else { state with storage := .placeholder }
  else state

def unloadSharedStorage (_storage : Storage) : Storage := .absent

def updatePointShadow (state : State) (index : SlotIndex) : State :=
  let light := getSlot state index
  if pointShadowDemand light then
    let attached := setSlot state index { light with shadowReference := true }
    { attached with storage := .pointShadowArray }
  else state

def shadowEligible (state : State) (index : SlotIndex) (enabled : Bool) : Bool :=
  enabled && state.storage = .pointShadowArray &&
    (getSlot state index).used && (getSlot state index).castsShadows &&
    !(getSlot state index).sun &&
    (getSlot state index).shadowReference

def usedCount (state : State) : Nat :=
  (if state.slot0.used then 1 else 0) + (if state.slot1.used then 1 else 0)

-- The shader uniform span is highest-used heap index plus one, not used count.
def shaderSpan (state : State) : Nat :=
  if state.slot1.used then 2 else if state.slot0.used then 1 else 0

def pointShadowSlotCapacity : Nat := 64
def pointShadowFacesPerSlot : Nat := 6
def pointShadowLayerCapacity : Nat :=
  pointShadowSlotCapacity * pointShadowFacesPerSlot

def rawPointShadowLayer (slot face : Nat) : Nat :=
  slot * pointShadowFacesPerSlot + face

def pointShadowLayer (slot face : Nat) : Nat :=
  rawPointShadowLayer slot face

def checkedPointShadowLayer (slot face : Nat) : Option Nat :=
  if slot < pointShadowSlotCapacity && face < pointShadowFacesPerSlot then
    some (pointShadowLayer slot face)
  else none

def gfxLightHeapCapacity : Nat := 128

def slotOrdinal (index : SlotIndex) : Nat :=
  match index with
  | .zero => 0
  | .one => 1

def shadowLayer (index : SlotIndex) (face : Nat) : Nat :=
  pointShadowLayer (slotOrdinal index) face

def bothLive : State :=
  ⟨.pointShadowArray,
    ⟨true, true, false, true⟩,
    ⟨true, true, false, true⟩⟩

theorem non_point_light_has_no_array_demand (light : LightSlot)
    (notPointCaster : light.used = false ∨ light.castsShadows = false ∨ light.sun = true) :
    pointShadowDemand light = false := by
  rcases notPointCaster with unused | notCasting | sun
  · simp [pointShadowDemand, unused]
  · simp [pointShadowDemand, notCasting]
  · simp [pointShadowDemand, sun]

theorem array_demand_is_the_two_slot_disjunction (state : State) :
    stateNeedsPointShadowArray state = true ↔
      pointShadowDemand state.slot0 = true ∨ pointShadowDemand state.slot1 = true := by
  simp [stateNeedsPointShadowArray]

theorem lazy_array_demand_success (state : State)
    (absent : state.storage = .absent)
    (demand : stateNeedsPointShadowArray state = true) :
    (initializeLazyStorage state true).storage = .pointShadowArray := by
  simp [initializeLazyStorage, absent, demand, initializeSharedArray]

theorem lazy_no_demand_selects_placeholder (state : State)
    (absent : state.storage = .absent)
    (noDemand : stateNeedsPointShadowArray state = false) :
    (initializeLazyStorage state false).storage = .placeholder := by
  simp [initializeLazyStorage, absent, noDemand]

theorem lazy_demand_failure_remains_retryable (state : State)
    (absent : state.storage = .absent)
    (demand : stateNeedsPointShadowArray state = true) :
    (initializeLazyStorage state false).storage = .absent ∧
    (initializeLazyStorage (initializeLazyStorage state false) true).storage =
      .pointShadowArray := by
  have failed : initializeLazyStorage state false = { state with storage := .absent } := by
    simp [initializeLazyStorage, absent, demand, initializeSharedArray]
  constructor
  · rw [failed]
  · rw [failed]
    exact lazy_array_demand_success { state with storage := .absent } rfl demand

theorem lazy_scan_detects_caster_in_either_slot :
    stateNeedsPointShadowArray
      ⟨.absent, ⟨true, true, false, false⟩, emptySlot⟩ = true ∧
    stateNeedsPointShadowArray
      ⟨.absent, emptySlot, ⟨true, true, false, false⟩⟩ = true := by
  decide

theorem lazy_scan_ignores_sun_and_unused_casters :
    stateNeedsPointShadowArray
      ⟨.absent, ⟨true, true, true, false⟩, ⟨false, true, false, false⟩⟩ = false := by
  decide

theorem add_uses_first_empty_slot :
    (addFirstEmpty emptyState).2 = some .zero ∧
    (addFirstEmpty emptyState).1.slot0 = freshLight := by
  simp [addFirstEmpty, emptyState, emptySlot, freshLight, setSlot]

theorem add_uses_second_slot_when_first_is_live :
    (addFirstEmpty { emptyState with slot0 := freshLight }).2 = some .one ∧
    (addFirstEmpty { emptyState with slot0 := freshLight }).1.slot0 = freshLight ∧
    (addFirstEmpty { emptyState with slot0 := freshLight }).1.slot1 = freshLight := by
  simp [addFirstEmpty, emptyState, emptySlot, freshLight, setSlot]

theorem full_heap_add_is_noop (state : State)
    (used0 : state.slot0.used = true) (used1 : state.slot1.used = true) :
    addFirstEmpty state = (state, none) := by
  simp [addFirstEmpty, used0, used1]

theorem remove_lower_slot_preserves_heap_hole (state : State) :
    (removeLight state .zero).slot0.used = false := by
  simp [removeLight, getSlot, setSlot, detach]

theorem hole_keeps_heap_indexed_shader_span :
    let after := removeLight bothLive .zero
    usedCount after = 1 ∧ shaderSpan after = 2 ∧
    shadowEligible after .zero true = false ∧
    shadowEligible after .one true = true := by
  decide

theorem add_reuses_hole_with_clean_shadow_state :
    let afterRemove := removeLight bothLive .zero
    let (afterAdd, index) := addFirstEmpty afterRemove
    index = some .zero ∧
    afterAdd.slot0 = freshLight ∧
    afterAdd.slot1 = bothLive.slot1 ∧
    shaderSpan afterAdd = 2 ∧
    shadowEligible afterAdd .zero true = false := by
  decide

  theorem removing_light_detaches_only_its_borrowed_reference
    (storage : Storage) (other : LightSlot) :
    let state : State := ⟨storage, ⟨true, true, false, true⟩, other⟩
    let next := removeLight state .zero
    next.storage = storage ∧
    next.slot0.used = false ∧
    next.slot0.shadowReference = false ∧
    next.slot1 = other := by
  cases storage <;> simp [removeLight, getSlot, setSlot, detach]

theorem remove_all_keeps_shared_storage_and_detaches_slots
    (storage : Storage) (first second : LightSlot) :
    let next := removeAll ⟨storage, first, second⟩
    next.storage = storage ∧
    next.slot0.used = false ∧ next.slot0.shadowReference = false ∧
    next.slot1.used = false ∧ next.slot1.shadowReference = false := by
  cases first <;> cases second <;> cases storage <;>
    simp [removeAll, detach]

theorem absent_storage_gets_placeholder (first second : LightSlot) :
    ensurePlaceholder ⟨.absent, first, second⟩ =
      ⟨.placeholder, first, second⟩ := by
  simp [ensurePlaceholder]

theorem initialized_storage_is_preserved (storage : Storage)
    (first second : LightSlot) (notAbsent : storage ≠ .absent) :
    ensurePlaceholder ⟨storage, first, second⟩ =
      ⟨storage, first, second⟩ := by
  cases storage <;> simp_all [ensurePlaceholder]

theorem absent_array_failure_remains_retryable :
    initializeSharedArray .absent false = .absent ∧
    initializeSharedArray .absent true = .pointShadowArray := by
  decide

theorem placeholder_upgrade_failure_remains_retryable :
    let failed := initializeSharedArray .placeholder false
    failed = .absent ∧
    initializeSharedArray failed true = .pointShadowArray := by
  decide

theorem unload_clears_any_shared_storage (storage : Storage) :
    unloadSharedStorage storage = .absent := by
  rfl

theorem unload_shared_storage_is_idempotent (storage : Storage) :
    unloadSharedStorage (unloadSharedStorage storage) =
      unloadSharedStorage storage := by
  rfl

theorem placeholder_promotes_and_point_caster_attaches :
    let state : State := ⟨.placeholder, ⟨true, true, false, false⟩, emptySlot⟩
    let next := updatePointShadow state .zero
    next.storage = .pointShadowArray ∧
    next.slot0.shadowReference = true ∧
    shadowEligible next .zero true = true := by
  decide

theorem non_point_shadow_light_does_not_allocate (state : State)
    (index : SlotIndex) (notPointCaster :
      let light := getSlot state index
      light.used = false ∨ light.castsShadows = false ∨ light.sun = true) :
    updatePointShadow state index = state := by
  cases index with
  | zero =>
      cases used : state.slot0.used <;>
        cases casts : state.slot0.castsShadows <;>
        cases sunValue : state.slot0.sun <;>
          simp_all [updatePointShadow, getSlot, pointShadowDemand]
  | one =>
      cases used : state.slot1.used <;>
        cases casts : state.slot1.castsShadows <;>
        cases sunValue : state.slot1.sun <;>
          simp_all [updatePointShadow, getSlot, pointShadowDemand]

theorem layer_bands_fit_two_slot_array (index : SlotIndex) (face : Nat)
    (faceBound : face < 6) : shadowLayer index face < 12 := by
  cases index <;>
  simp [shadowLayer, slotOrdinal, pointShadowLayer, rawPointShadowLayer,
      pointShadowFacesPerSlot] <;> omega

theorem different_slots_use_disjoint_faces (face0 face1 : Nat)
    (face0Bound : face0 < 6) (face1Bound : face1 < 6) :
    shadowLayer .zero face0 ≠ shadowLayer .one face1 := by
  simp [shadowLayer, slotOrdinal, pointShadowLayer, rawPointShadowLayer,
    pointShadowFacesPerSlot]
  omega

theorem point_shadow_layer_capacity_is_384 :
    pointShadowLayerCapacity = 384 := by
  decide

theorem raw_point_shadow_layer_within_capacity (slot face : Nat)
    (slotBound : slot < pointShadowSlotCapacity)
    (faceBound : face < pointShadowFacesPerSlot) :
    rawPointShadowLayer slot face < pointShadowLayerCapacity := by
  unfold rawPointShadowLayer pointShadowLayerCapacity pointShadowSlotCapacity
    pointShadowFacesPerSlot
  simp [pointShadowSlotCapacity, pointShadowFacesPerSlot] at *
  omega

theorem point_shadow_layer_within_capacity (slot face : Nat)
    (slotBound : slot < pointShadowSlotCapacity)
    (faceBound : face < pointShadowFacesPerSlot) :
    pointShadowLayer slot face < pointShadowLayerCapacity := by
  exact raw_point_shadow_layer_within_capacity slot face slotBound faceBound

theorem point_shadow_layers_are_injective
    (slotA slotB faceA faceB : Nat)
    (faceABound : faceA < pointShadowFacesPerSlot)
    (faceBBound : faceB < pointShadowFacesPerSlot)
    (sameLayer : pointShadowLayer slotA faceA = pointShadowLayer slotB faceB) :
    slotA = slotB ∧ faceA = faceB := by
  simp [pointShadowFacesPerSlot] at faceABound faceBBound
  unfold pointShadowLayer rawPointShadowLayer pointShadowFacesPerSlot at sameLayer
  constructor <;> omega

theorem distinct_valid_slots_do_not_alias
    (slotA slotB faceA faceB : Nat)
    (faceABound : faceA < pointShadowFacesPerSlot)
    (faceBBound : faceB < pointShadowFacesPerSlot)
    (differentSlots : slotA ≠ slotB) :
    pointShadowLayer slotA faceA ≠ pointShadowLayer slotB faceB := by
  intro sameLayer
  exact differentSlots (point_shadow_layers_are_injective slotA slotB faceA faceB
    faceABound faceBBound sameLayer).1

theorem different_faces_in_one_valid_slot_do_not_alias
    (slot faceA faceB : Nat)
    (faceABound : faceA < pointShadowFacesPerSlot)
    (faceBBound : faceB < pointShadowFacesPerSlot)
    (differentFaces : faceA ≠ faceB) :
    pointShadowLayer slot faceA ≠ pointShadowLayer slot faceB := by
  intro sameLayer
  exact differentFaces (point_shadow_layers_are_injective slot slot faceA faceB
    faceABound faceBBound sameLayer).2

theorem raw_slot_64_starts_outside_capacity (face : Nat) :
    rawPointShadowLayer pointShadowSlotCapacity face ≥
      pointShadowLayerCapacity := by
  unfold rawPointShadowLayer pointShadowLayerCapacity pointShadowSlotCapacity
    pointShadowFacesPerSlot
  omega

theorem checked_draw_layer_within_capacity (slot face layer : Nat)
    (checked : checkedPointShadowLayer slot face = some layer) :
    layer < pointShadowLayerCapacity := by
  by_cases slotBound : slot < pointShadowSlotCapacity
  · by_cases faceBound : face < pointShadowFacesPerSlot
    · simp [checkedPointShadowLayer, slotBound, faceBound] at checked
      cases checked
      exact point_shadow_layer_within_capacity slot face slotBound faceBound
    · simp [checkedPointShadowLayer, slotBound, faceBound] at checked
  · simp [checkedPointShadowLayer, slotBound] at checked

theorem overflow_shadow_slot_is_skipped (slot face : Nat)
    (overflow : pointShadowSlotCapacity ≤ slot) :
    checkedPointShadowLayer slot face = none := by
  have slotOut : ¬ slot < pointShadowSlotCapacity := by omega
  simp [checkedPointShadowLayer, slotOut]

theorem configured_light_heap_exceeds_shadow_capacity :
    pointShadowSlotCapacity < gfxLightHeapCapacity := by
  decide

theorem first_overflow_heap_slot_is_skipped :
    pointShadowSlotCapacity < gfxLightHeapCapacity ∧
    checkedPointShadowLayer pointShadowSlotCapacity 0 = none := by
  decide

end GxProofs.GfxLightShadowSlots
