/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingCrossingBoundarySourceKeyPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData

/-! # Canonical-left source-key candidates of crossing slots -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Canonical crossing record represented by one affine slot at a runtime
descriptor pair. -/
def Slot.canonicalCrossingRecord
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :
    CrossingRecord :=
  occurrencePairCrossingRecordAtPeriod pair.1.gridSize
    (slot.occurrences.1.evalPair .first pair,
      slot.occurrences.2.evalPair .second pair)

/-- The compact canonical-left boundary identity of that record. -/
def Slot.canonicalLeftSourceKeyPair
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :
    CarrierNodeSourceKeys.SourceKeyPair :=
  RetainedCompactAtomWords.crossingPair
    (slot.canonicalCrossingRecord pair)

/-- One always-supported canonical-left boundary template per crossing slot. -/
def Slot.canonicalLeftCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :
    List (Template CarrierNode) :=
  [⟨.boundary
      ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
          (slot.canonicalCrossingRecord pair) (0, 0), .left⟩,
    true⟩]

def canonicalLeftCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierNode)) :=
  crossingSlots.map (Slot.canonicalLeftCarrierNodeTemplateBlock pair)

/-- Padded canonical-left carrier nodes selected by the crossing activations. -/
def canonicalLeftCarrierNodeCandidates
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List (Candidate CarrierNode) :=
  candidates (crossingActivations (descriptorSlotPairTokens pair))
    (canonicalLeftCarrierNodeTemplateBlocks (pair.1.1, pair.2.1))

/-- One optional compact canonical-left pair per fixed crossing slot. -/
def canonicalLeftSourceKeyCandidates
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List (Candidate CarrierNodeSourceKeys.SourceKeyPair) :=
  (canonicalLeftCarrierNodeCandidates pair).map
    CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
