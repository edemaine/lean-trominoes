/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftSlotData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyCandidateData

/-! # Canonical-left source-key candidates of common-shift slots -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- One always-supported canonical-left boundary template per shifted slot. -/
def canonicalCrossingShiftLeftCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template CarrierNode)) :=
  canonicalCrossingShiftSlots.map
    (Slot.canonicalLeftCarrierNodeTemplateBlock pair)

/-- Padded canonical-left nodes selected by the complete shift schedule. -/
def canonicalCrossingShiftLeftCarrierNodeCandidates
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List (Candidate CarrierNode) :=
  candidates
    (canonicalCrossingShiftSlots.map fun slot =>
      slot.evalTokens (descriptorSlotPairTokens pair))
    (canonicalCrossingShiftLeftCarrierNodeTemplateBlocks
      (pair.1.1, pair.2.1))

/-- One optional compact canonical-left pair per shifted crossing slot. -/
def canonicalCrossingShiftLeftSourceKeyCandidates
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List (Candidate CarrierNodeSourceKeys.SourceKeyPair) :=
  (canonicalCrossingShiftLeftCarrierNodeCandidates pair).map
    CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
