/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Padded compact source-key candidates and representative rows -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords

/-- Compact source-key identities in exact padded carrier-node slot order. -/
def paddedCarrierSourceKeyCandidateStream
    (descriptors : List RouteDescriptor) :=
  (paddedCarrierNodeCandidateStream descriptors).map
    CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate

/-- Guarded compact source-key words followed by the rejection sentinel. -/
def paddedCarrierSourceKeyWordsWithSentinel
    (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  wordsWithSentinel CarrierNodeSourceKeys.word
    (paddedCarrierSourceKeyCandidateStream descriptors)

/-- Sentinel-free representative rows of compact source-key identities. -/
def paddedCarrierSourceKeyRepresentativeRows
    (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  representativeRows CarrierNodeSourceKeys.word
    (paddedCarrierSourceKeyCandidateStream descriptors)

end LeanTrominoes.PeriodicOrthocrossing
