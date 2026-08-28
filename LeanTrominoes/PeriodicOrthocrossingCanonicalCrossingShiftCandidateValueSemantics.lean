/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PaddedSupportedCandidateBlockMappedSelection
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftSlotSemantics

/-! # Active values of common-shift canonical-left candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

private theorem filterMap_sourceKeyCandidates
    (candidates : List (Candidate CarrierNode)) :
    (candidates.map
        CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).filterMap
        Candidate.value =
      (candidates.filterMap Candidate.value).map
        CarrierNodeSourceKeys.pair := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate,
          induction]

/-- Compacting the padded shifted carrier-node candidates keeps exactly the
left boundary belonging to every active shifted slot. -/
theorem canonicalCrossingShiftLeftCarrierNodeActiveValues_eq
    (pair : TaggedDescriptor × TaggedDescriptor) :
    activeValues
        (canonicalCrossingShiftSlots.map fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair))
        (canonicalCrossingShiftLeftCarrierNodeTemplateBlocks
          (pair.1.1, pair.2.1)) =
      (canonicalCrossingShiftSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).map fun slot =>
          CarrierNode.boundary
            ⟨slot.canonicalCrossingRecord (pair.1.1, pair.2.1), .left⟩ := by
  unfold canonicalCrossingShiftLeftCarrierNodeTemplateBlocks
  rw [activeValues_map_eq_filter_flatMap]
  let activeSlots := canonicalCrossingShiftSlots.filter fun slot =>
    slot.evalTokens (descriptorSlotPairTokens pair)
  calc
    activeSlots.flatMap (fun slot =>
        (slot.canonicalLeftCarrierNodeTemplateBlock
          (pair.1.1, pair.2.1)).map Template.value) =
      activeSlots.flatMap (fun slot =>
        [CarrierNode.boundary
          ⟨slot.canonicalCrossingRecord (pair.1.1, pair.2.1), .left⟩]) := by
        apply List.flatMap_congr
        intro slot _slotMember
        simp [Slot.canonicalLeftCarrierNodeTemplateBlock,
          crossingRecordPeriodTranslateAtPeriod, Cell.add, Cell.scale]
    _ = activeSlots.map (fun slot =>
        CarrierNode.boundary
          ⟨slot.canonicalCrossingRecord (pair.1.1, pair.2.1), .left⟩) := by
        induction activeSlots with
        | nil => rfl
        | cons slot slots induction => simp [induction]

/-- Compacting the projected source-key candidates keeps exactly one
canonical-left compact identity for every active shifted slot. -/
theorem filterMap_canonicalCrossingShiftLeftSourceKeyCandidates_eq_slots
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (canonicalCrossingShiftLeftSourceKeyCandidates pair).filterMap
        Candidate.value =
      (canonicalCrossingShiftSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).map fun slot =>
          slot.canonicalLeftSourceKeyPair (pair.1.1, pair.2.1) := by
  unfold canonicalCrossingShiftLeftSourceKeyCandidates
  rw [filterMap_sourceKeyCandidates]
  unfold canonicalCrossingShiftLeftCarrierNodeCandidates
  rw [
    filterMap_value_candidates,
    canonicalCrossingShiftLeftCarrierNodeActiveValues_eq,
    List.map_map]
  apply List.map_congr_left
  intro slot _slotMember
  simp [Slot.canonicalLeftSourceKeyPair,
    RetainedCompactAtomWords.crossingPair,
    RetainedCompactAtomWords.carrierPair,
    RetainedCompactAtomWords.zeroCarrierNode]

/-- Under the two selected local shapes, compacted shifted-slot candidates
are exactly the semantic common-shift candidates mapped to their normalized
canonical-left identities. -/
theorem filterMap_canonicalCrossingShiftLeftSourceKeyCandidates_eq_shiftCandidates_of_matches
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    (canonicalCrossingShiftLeftSourceKeyCandidates pair).filterMap
        Candidate.value =
      (carrierCrossingRetentionShifts.filterMap
        (canonicalShiftCandidateAtPeriod pair.1.1.gridSize pair)).map
          (fun occurrencePair =>
            RetainedCompactAtomWords.crossingPair
              (occurrencePairCrossingRecordAtPeriod
                pair.1.1.gridSize occurrencePair)) := by
  rw [filterMap_canonicalCrossingShiftLeftSourceKeyCandidates_eq_slots]
  have shiftedPairs :=
    map_filter_canonicalCrossingShiftSlots_eq_candidates_of_matches
      firstShape secondShape pair firstMatches secondMatches
  have mapped := congrArg
    (List.map fun occurrencePair =>
      RetainedCompactAtomWords.crossingPair
        (occurrencePairCrossingRecordAtPeriod
          pair.1.1.gridSize occurrencePair)) shiftedPairs
  simpa [List.map_map, Function.comp_def,
    Slot.canonicalLeftSourceKeyPair,
    Slot.canonicalCrossingRecord] using mapped

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
