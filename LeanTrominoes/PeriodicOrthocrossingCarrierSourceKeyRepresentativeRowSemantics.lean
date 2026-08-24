/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCandidateCorrectSupport

/-! # Representative rows of compact carrier source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

theorem paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows
    (descriptors : List RouteDescriptor) :
    paddedCarrierSourceKeyRepresentativeRows descriptors =
      selectedRows (paddedCarrierSourceKeyCandidateStream descriptors) := by
  unfold paddedCarrierSourceKeyRepresentativeRows
  apply representativeRows_eq_selectedRows
    CarrierNodeSourceKeys.word CarrierNodeSourceKeys.word_injective
    ((paddedCarrierSourceKeyCandidateStream descriptors).filterMap
      Candidate.value)
  exact paddedCarrierSourceKeyCandidateStream_correctSupport descriptors

end LeanTrominoes.PeriodicOrthocrossing
