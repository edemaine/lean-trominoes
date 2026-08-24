/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyGlobalSupport

/-! # Support of affine occurrence-pair carrier-key templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- Every template in one retained-shift block carries its exact global
terminal-stream membership bit. -/
theorem occurrencePairCrossingCarrierKeyShiftTemplateBlock_correct
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
    (shift : Cell) :
    ∀ template ∈ occurrencePairCrossingCarrierKeyShiftTemplateBlock
        pair occurrences shift,
      template.supported = decide (template.value ∈
        occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors)) := by
  have firstCorrect :=
    occurrences.1.carrierKeyAtShiftSupported_eq_mem_globalTerminal
      descriptors selfIndexed firstShape .first pair firstMatches
      firstDescriptorMember firstOccurrenceMember shift
  have secondCorrect :=
    occurrences.2.carrierKeyAtShiftSupported_eq_mem_globalTerminal
      descriptors selfIndexed secondShape .second pair secondMatches
      secondDescriptorMember secondOccurrenceMember shift
  let first : Template (Nat × Nat × Cell) :=
    ⟨occurrences.1.carrierKeyAtShift .first pair shift,
      occurrences.1.carrierKeyAtShiftSupported shift⟩
  let second : Template (Nat × Nat × Cell) :=
    ⟨occurrences.2.carrierKeyAtShift .second pair shift,
      occurrences.2.carrierKeyAtShiftSupported shift⟩
  intro template templateMember
  change template ∈ [first, first, second, second] at templateMember
  simp only [List.mem_cons, List.not_mem_nil, or_false]
    at templateMember
  rcases templateMember with
    firstEq | firstEq | secondEq | secondEq
  · subst template
    exact firstCorrect
  · subst template
    exact firstCorrect
  · subst template
    exact secondCorrect
  · subst template
    exact secondCorrect

/-- The complete retained-shift family of one matched occurrence pair has
exact global terminal support. -/
theorem occurrencePairCrossingCarrierKeyTemplateBlock_correct
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
      secondShape.occurrences .second) :
    ∀ template ∈ occurrencePairCrossingCarrierKeyTemplateBlock
        pair occurrences,
      template.supported = decide (template.value ∈
        occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors)) := by
  intro template templateMember
  unfold occurrencePairCrossingCarrierKeyTemplateBlock at templateMember
  rw [List.mem_flatMap] at templateMember
  rcases templateMember with ⟨shift, _shiftMember, templateMember⟩
  exact occurrencePairCrossingCarrierKeyShiftTemplateBlock_correct
    descriptors selfIndexed firstShape secondShape pair
    firstMatches secondMatches firstDescriptorMember
    secondDescriptorMember occurrences firstOccurrenceMember
    secondOccurrenceMember shift template templateMember

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
