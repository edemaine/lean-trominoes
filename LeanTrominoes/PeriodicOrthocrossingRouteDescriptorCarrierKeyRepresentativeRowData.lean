/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData

/-! # Guarded carrier-key words and representative rows -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords

/-- Guarded words for the complete padded terminal-plus-crossing candidate
stream, followed by the explicit rejection sentinel. -/
def paddedCarrierKeyWordsWithSentinel
    (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  wordsWithSentinel CarrierKeyWords.word
    (paddedCarrierKeyCandidateStream descriptors)

/-- Sentinel-free last-representative rows of the complete guarded carrier-
key candidate stream. -/
def paddedCarrierKeyRepresentativeRows
    (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  representativeRows CarrierKeyWords.word
    (paddedCarrierKeyCandidateStream descriptors)

end LeanTrominoes.PeriodicOrthocrossing
