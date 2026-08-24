/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateStreamData

/-! # Active carrier identities and their representative rows -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords

/-- Guarded active-identity words followed by the explicit rejection
sentinel used by the representative-square compiler. -/
def paddedCarrierIdentityWordsWithSentinelAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  wordsWithSentinel CarrierNodeCodeWords.word
    (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors)

/-- Last-occurrence rows selecting one active slot for each distinct carrier
identity. -/
def paddedCarrierIdentityRepresentativeRowsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  representativeRows CarrierNodeCodeWords.word
    (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors)

end LeanTrominoes.PeriodicOrthocrossing

end
