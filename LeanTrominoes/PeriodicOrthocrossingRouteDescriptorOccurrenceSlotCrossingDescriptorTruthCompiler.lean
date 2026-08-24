/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Batched descriptor truth values for occurrence-slot crossings -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- Evaluate the descriptor portion of every crossing slot after deleting the
twelfth field. -/
def descriptorTruthValues
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  predicateListTruthValues
    (crossingSlots.map Slot.descriptorPredicate)
    (descriptorTokens tokens)

/-- Descriptor truth values remain a single compact batched affine scan after
the finite descriptor projection. -/
noncomputable def descriptorTruthValuesComputableInPolyTime :
    TM2ComputableInPolyTime id id descriptorTruthValues := by
  change TM2ComputableInPolyTime id id
    (fun tokens =>
      predicateListTruthValues
        (crossingSlots.map Slot.descriptorPredicate)
        (descriptorTokens tokens))
  exact TM2CompositionMachine.computableInPolyTime
    descriptorTokensComputableInPolyTime
    (predicateListTruthValuesComputableInPolyTime
      (crossingSlots.map Slot.descriptorPredicate))

/-- The compact descriptor evaluator returns one semantic affine truth value
for every crossing slot, in exact alignment order. -/
@[simp] theorem descriptorTruthValues_eq
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    descriptorTruthValues tokens =
      crossingSlots.map fun slot =>
        slot.descriptorPredicate.evalTokens (descriptorTokens tokens) := by
  unfold descriptorTruthValues
  rw [predicateListTruthValues_eq, List.map_map]
  rfl

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
