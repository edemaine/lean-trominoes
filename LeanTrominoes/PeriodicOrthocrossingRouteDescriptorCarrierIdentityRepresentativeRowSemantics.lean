/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityRepresentativeRowData

/-! # Exact representative rows of padded carrier identities -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

/-- Squaring the guarded identity words and retaining their final occurrences
selects exactly one active padded slot for every distinct carrier node. -/
theorem paddedCarrierIdentityRepresentativeRows_eq_selectedRows
    (period : Nat) (descriptors : List RouteDescriptor) :
    paddedCarrierIdentityRepresentativeRowsAtPeriod period descriptors =
      selectedRows
        (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors) := by
  unfold paddedCarrierIdentityRepresentativeRowsAtPeriod
  apply representativeRows_eq_selectedRows
    CarrierNodeCodeWords.word CarrierNodeCodeWords.word_injective
    ((paddedCarrierIdentityCandidateStreamAtPeriod
      period descriptors).filterMap Candidate.value)
  exact paddedCarrierIdentityCandidateStream_correctSupport
    period descriptors

end LeanTrominoes.PeriodicOrthocrossing
