/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisShiftSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeData

/-! # Axis semantics of one crossing occurrence pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

private theorem forall₂_append
    {First Second : Type*} {Relation : First → Second → Prop}
    {firstHead firstTail : List First}
    {secondHead secondTail : List Second}
    (head : List.Forall₂ Relation firstHead secondHead)
    (tail : List.Forall₂ Relation firstTail secondTail) :
    List.Forall₂ Relation
      (firstHead ++ firstTail) (secondHead ++ secondTail) := by
  induction head with
  | nil => exact tail
  | cons relation rest induction =>
      exact List.Forall₂.cons relation induction

/-- The complete retained-shift recipe axes of one canonical-oriented
occurrence pair agree with its carrier-key template datum. -/
theorem occurrencePairCrossingCarrierKeyTemplateBlock_axisDatum_of_axes
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : firstShape.Matches pair.1)
    (secondMatches : secondShape.Matches pair.2)
    (firstDescriptorMember : pair.1 ∈ descriptors)
    (secondDescriptorMember : pair.2 ∈ descriptors)
    (occurrences : Occurrence × Occurrence)
    (firstOccurrenceMember : occurrences.1 ∈
      firstShape.occurrences .first)
    (secondOccurrenceMember : occurrences.2 ∈
      secondShape.occurrences .second)
    (firstHorizontal :
      (occurrences.1.evalPair .first pair).1.segment.IsHorizontal)
    (secondVertical :
      (occurrences.2.evalPair .second pair).1.segment.IsVertical) :
    List.Forall₂
      (fun axis template =>
        FixedAxisUnaryFields.value true axis =
          RouteDescriptorCarrierKeyAxisDatum.value descriptors
            (some template.value))
      ((occurrencePairCrossingCarrierKeyRecipeBlock occurrences).map fun recipe =>
        decide (recipe.side = .first))
      (occurrencePairCrossingCarrierKeyTemplateBlock pair occurrences) := by
  unfold occurrencePairCrossingCarrierKeyRecipeBlock
    occurrencePairCrossingCarrierKeyTemplateBlock
  rw [List.map_flatMap]
  induction carrierCrossingRetentionShifts with
  | nil => exact List.Forall₂.nil
  | cons shift shifts induction =>
      simp only [List.flatMap_cons]
      apply forall₂_append
      · simpa [occurrencePairCrossingCarrierKeyShiftRecipeBlock,
          Occurrence.carrierKeyRecipeAtShift] using
          occurrencePairCrossingCarrierKeyShiftTemplateBlock_axisDatum_of_axes
            descriptors selfIndexed firstShape secondShape pair
            firstMatches secondMatches firstDescriptorMember
            secondDescriptorMember occurrences firstOccurrenceMember
            secondOccurrenceMember firstHorizontal secondVertical shift
      · exact induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
