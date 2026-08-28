/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthBooleanWordAnd
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingDescriptorTruthCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotGuardBatchCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime

/-! # Batched truth compiler for arbitrary fixed crossing-slot lists -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- Evaluate the affine descriptor predicate of every slot in a fixed list. -/
def descriptorTruthValuesFor (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  predicateListTruthValues (slots.map Slot.descriptorPredicate)
    (descriptorTokens tokens)

noncomputable def descriptorTruthValuesForComputableInPolyTime
    (slots : List Slot) :
    TM2ComputableInPolyTime id id (descriptorTruthValuesFor slots) := by
  change TM2ComputableInPolyTime id id
    (fun tokens =>
      predicateListTruthValues (slots.map Slot.descriptorPredicate)
        (descriptorTokens tokens))
  exact TM2CompositionMachine.computableInPolyTime
    descriptorTokensComputableInPolyTime
    (predicateListTruthValuesComputableInPolyTime
      (slots.map Slot.descriptorPredicate))

/-- Descriptor and runtime-slot truth words evaluated independently on the
same twelve-field pair block. -/
def componentTruthValuesFor (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool × List Bool :=
  (descriptorTruthValuesFor slots tokens,
    SlotGuardBatch.truthValues slots tokens)

/-- Pointwise conjunction of the two fixed aligned truth words. -/
def truthValuesFor (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  FixedLengthBooleanWordAnd.output slots.length
    (componentTruthValuesFor slots tokens)

/-- Any fixed crossing-slot list is evaluated by one projected affine scan,
one finite-state slot counter, and a fixed-length conjunction. -/
noncomputable def truthValuesForComputableInPolyTime
    (slots : List Slot) :
    TM2ComputableInPolyTime id id (truthValuesFor slots) := by
  let components := TM2ForkMachine.computableInPolyTime
    (descriptorTruthValuesForComputableInPolyTime slots)
    (SlotGuardBatch.truthValuesComputableInPolyTime slots)
  change TM2ComputableInPolyTime id id
    (fun tokens => FixedLengthBooleanWordAnd.output slots.length
      (componentTruthValuesFor slots tokens))
  exact TM2CompositionMachine.computableInPolyTime components
    (FixedLengthBooleanWordAnd.outputComputableInPolyTime slots.length)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
