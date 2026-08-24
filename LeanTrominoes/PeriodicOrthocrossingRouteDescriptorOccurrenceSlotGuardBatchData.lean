/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData

/-! # Finite-control batch evaluation of occurrence-slot guards -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing
namespace SlotGuardBatch

open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Saturated counts `0, …, 81`; the last value also represents overflow
beyond every valid slot index. -/
abbrev Count := Fin 82

structure Control where
  first : Count
  second : Count
  deriving DecidableEq, Fintype

instance : Inhabited Control := ⟨⟨0, 0⟩⟩

def initial : Control := ⟨0, 0⟩

/-- Add a natural count, saturating at the overflow value 81. -/
def addCount (count : Count) (amount : Nat) : Count :=
  ⟨min (count.val + amount) 81, by omega⟩

/-- Count only units in the twelfth field, separately for the two pair
sides. -/
def transition : Control →
    RouteDescriptorOccurrenceSlotPairFieldTags.Token →
    Control × List Bool
  | control, .unit .first field =>
      if field.val = 11 then
        ({ control with first := addCount control.first 1 }, [])
      else
        (control, [])
  | control, .unit .second field =>
      if field.val = 11 then
        ({ control with second := addCount control.second 1 }, [])
      else
        (control, [])
  | control, _ => (control, [])

/-- Emit the complete fixed slot-guard truth word from the two final counts. -/
def finish (slots : List Slot) (control : Control) : List Bool :=
  slots.map fun slot =>
    decide (control.first.val = slot.firstSlot) &&
      decide (control.second.val = slot.secondSlot)

/-- Batched physical evaluation of a fixed slot-guard list. -/
def truthValues (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  FiniteStateTransducer.output initial transition (finish slots) tokens

/-- Slot-guard truth word aligned with the complete affine crossing scan. -/
def crossingTruthValues
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  truthValues crossingSlots tokens

end SlotGuardBatch
end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
