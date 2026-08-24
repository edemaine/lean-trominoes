/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeSemantics

/-! # Activity-supported key words of padded carrier nodes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

theorem TerminalActiveCarrierKeyRecipeStream.guardedWords_eq_paddedCandidates
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    TerminalActiveCarrierKeyRecipeStream.guardedWords pairs =
      ((pairs.flatMap
        RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates).map
          (Candidate.mapActiveValue CarrierNode.carrierKey)).map
            (guardedWord CarrierKeyWords.word) := by
  unfold TerminalActiveCarrierKeyRecipeStream.guardedWords
  rw [List.map_map, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  rw [RouteDescriptorPairAffine.terminalActiveCarrierKeyGuardedWords_descriptorPairTokens]
  rw [List.map_map]

theorem CrossingActiveCarrierKeyRecipeStream.guardedWords_eq_paddedCandidates
    (pairs : List
      (RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
        RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor)) :
    CrossingActiveCarrierKeyRecipeStream.guardedWords pairs =
      ((pairs.flatMap
        RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates).map
          (Candidate.mapActiveValue CarrierNode.carrierKey)).map
            (guardedWord CarrierKeyWords.word) := by
  unfold CrossingActiveCarrierKeyRecipeStream.guardedWords
  rw [List.map_map, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  rw [RouteDescriptorOccurrenceSlotCrossing.crossingActiveCarrierKeyGuardedWords_descriptorSlotPairTokens]
  rw [List.map_map]

/-- The complete compiled active-key word stream is exactly the guarded
physical-key projection of every padded carrier-node slot. -/
theorem CarrierActiveKeyRecipeStream.guardedWords_eq_paddedCarrierNodes
    (descriptors : List RouteDescriptor) :
    CarrierActiveKeyRecipeStream.guardedWords descriptors =
      ((paddedCarrierNodeCandidateStream descriptors).map
        (Candidate.mapActiveValue CarrierNode.carrierKey)).map
          (guardedWord CarrierKeyWords.word) := by
  unfold CarrierActiveKeyRecipeStream.guardedWords
    paddedCarrierNodeCandidateStream
    RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
  rw [TerminalActiveCarrierKeyRecipeStream.guardedWords_eq_paddedCandidates,
    CrossingActiveCarrierKeyRecipeStream.guardedWords_eq_paddedCandidates]
  simp [List.map_append]

end LeanTrominoes.PeriodicOrthocrossing

end
