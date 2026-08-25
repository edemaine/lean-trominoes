/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeOutputSemantics
import LeanTrominoes.PaddedSupportedCandidateRepresentativeSquareBridge
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowSemantics
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateListSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeRowCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalCandidateWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyCandidateStreamPairSemantics

/-! # Source-key words of carrier order-coordinate node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

namespace RouteDescriptorPairAffine

theorem componentWords_terminalDirectionalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (terminalDirectionalCarrierNodeCandidateStream descriptors)) =
      ⟨TerminalDirectionalSourceKeyStream.guardedComponentWords
        (descriptors ×ˢ descriptors)⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
    terminalDirectionalCarrierNodeCandidateStream
    TerminalDirectionalSourceKeyStream.guardedComponentWords
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair _pairMember
  have pairEq := congrArg DelimitedBinaryWords.Input.words
    (componentWords_terminalDirectionalCandidates pair)
  simpa [DelimitedBinaryWordGuardedPairMerge.componentWords,
    CarrierNodeSourceKeyCandidateWords.componentPairs] using pairEq

end RouteDescriptorPairAffine

namespace CarrierOrderCandidateKeyStream

/-- The raw component stream is exactly two source-key components per
semantic order-coordinate node candidate. -/
theorem componentWords_carrierOrderCandidateNodeStream
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (carrierOrderCandidateNodeStream descriptors)) =
      ⟨componentWords descriptors⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold carrierOrderCandidateNodeStream componentWords
    CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [List.map_append, List.flatMap_append]
  exact congrArg₂ (fun first second => first ++ second)
    (congrArg DelimitedBinaryWords.Input.words
      (RouteDescriptorPairAffine.componentWords_terminalDirectionalCarrierNodeCandidateStream
        descriptors))
    (congrArg DelimitedBinaryWords.Input.words
      (RouteDescriptorOccurrenceSlotCrossing.componentWords_paddedCrossingCarrierNodeCandidateStream
        descriptors))

/-- After adjacent-word merging, the compiler's keys are precisely the
guarded compact source identities of its semantic node candidates. -/
theorem guardedWords_carrierOrderCandidateNodeStream
    (descriptors : List RouteDescriptor) :
    guardedWords descriptors =
      (CarrierNodeSourceKeyCandidateWords.mergedWords
        (carrierOrderCandidateNodeStream descriptors)).words := by
  unfold guardedWords
  have componentEq := congrArg DelimitedBinaryWords.Input.words
    (componentWords_carrierOrderCandidateNodeStream descriptors)
  change
    (DelimitedBinaryWordGuardedPairMerge.componentWords
      (CarrierNodeSourceKeyCandidateWords.componentPairs
        (carrierOrderCandidateNodeStream descriptors))).words =
      componentWords descriptors at componentEq
  rw [← componentEq]
  rw [← CarrierNodeSourceKeyCandidateWords.guardedPairMergedWords_componentPairs]
  exact DelimitedBinaryWordGuardedPairMerge.mergeWords_componentWords
    (CarrierNodeSourceKeyCandidateWords.componentPairs
      (carrierOrderCandidateNodeStream descriptors))

theorem wordsWithSentinel_carrierOrderCandidateNodeStream
    (descriptors : List RouteDescriptor) :
    wordsWithSentinel descriptors =
      PaddedSupportedCandidateWords.wordsWithSentinel
        CarrierNodeSourceKeys.word
        ((carrierOrderCandidateNodeStream descriptors).map
          CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate) := by
  apply congrArg DelimitedBinaryWords.Input.mk
  rw [guardedWords_carrierOrderCandidateNodeStream]
  unfold CarrierNodeSourceKeyCandidateWords.mergedWords
  simp [List.map_map, Function.comp_def]

end CarrierOrderCandidateKeyStream

namespace CarrierOrderRepresentativeRows

/-- Generic representative squaring therefore yields the supported
source-identity rows of the semantic order-coordinate candidate stream. -/
theorem rows_eq_selectedRows_carrierOrderCandidateNodeStream
    (descriptors : List RouteDescriptor) :
    rows descriptors =
      selectedRows
        ((carrierOrderCandidateNodeStream descriptors).map
          CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate) := by
  unfold rows
  rw [CarrierOrderCandidateKeyStream.wordsWithSentinel_carrierOrderCandidateNodeStream]
  rw [dropLast_representativeSquareRows_eq]
  apply representativeRows_eq_selectedRows
    CarrierNodeSourceKeys.word CarrierNodeSourceKeys.word_injective
    (((carrierOrderCandidateNodeStream descriptors).map
      CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).filterMap
        Candidate.value)
  apply correctSupport_filterMap_of_supported_eq_isSome
  intro candidate candidateMember
  rcases List.mem_map.mp candidateMember with
    ⟨nodeCandidate, _nodeCandidateMember, rfl⟩
  rcases nodeCandidate with ⟨value, supported⟩
  cases value <;> rfl

end CarrierOrderRepresentativeRows
end LeanTrominoes.PeriodicOrthocrossing
