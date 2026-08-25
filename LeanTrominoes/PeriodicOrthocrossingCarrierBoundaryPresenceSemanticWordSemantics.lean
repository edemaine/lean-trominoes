/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyCandidateWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData

/-! # Semantic words for terminal/crossing presence streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

private theorem guardedWord_mapActiveValue_carrierKey
    (candidate : Candidate CarrierNode) :
    guardedWord CarrierKeyWords.word
        (candidate.mapActiveValue CarrierNode.carrierKey) =
      GuardedPresenceFieldProjector.semanticWord
        (candidate.value.map CarrierNode.carrierKey) := by
  rcases candidate with ⟨value, supported⟩
  cases value <;> rfl

theorem TerminalActiveCarrierKeyRecipeStream.guardedWords_eq_presenceSemanticWords
    (descriptors : List RouteDescriptor) :
    TerminalActiveCarrierKeyRecipeStream.guardedWords
        (descriptors ×ˢ descriptors) =
      (CarrierBoundaryPresenceField.terminalKeys descriptors).map
        GuardedPresenceFieldProjector.semanticWord := by
  rw [TerminalActiveCarrierKeyRecipeStream.guardedWords_eq_paddedCandidates]
  unfold CarrierBoundaryPresenceField.terminalKeys
    RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
  simp [PaddedSupportedLastRepresentativeEqualityRows.values,
    List.map_map, guardedWord_mapActiveValue_carrierKey]

theorem CrossingActiveCarrierKeyRecipeStream.guardedWords_eq_presenceSemanticWords
    (descriptors : List RouteDescriptor) :
    CrossingActiveCarrierKeyRecipeStream.guardedWords
        (RouteDescriptorOccurrenceSlotBinaryWords.taggedDescriptors
          descriptors ×ˢ
        RouteDescriptorOccurrenceSlotBinaryWords.taggedDescriptors
          descriptors) =
      (CarrierBoundaryPresenceField.crossingKeys descriptors).map
        GuardedPresenceFieldProjector.semanticWord := by
  rw [CrossingActiveCarrierKeyRecipeStream.guardedWords_eq_paddedCandidates]
  unfold CarrierBoundaryPresenceField.crossingKeys
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
  simp [PaddedSupportedLastRepresentativeEqualityRows.values,
    List.map_map, guardedWord_mapActiveValue_carrierKey]

end LeanTrominoes.PeriodicOrthocrossing

end
