/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Valid inputs for compact carrier representative lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeLookup

/-- Package compact representative rows with any exactly aligned value
stream as promised input to the generic lookup machine. -/
def input (alignedValues : List RouteDescriptor → List Nat)
    (alignedLength : ∀ descriptors,
      (alignedValues descriptors).length =
        (paddedCarrierSourceKeyCandidateStream descriptors).length + 1)
    (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (paddedCarrierSourceKeyRepresentativeRows descriptors).words
  values := alignedValues descriptors
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    ((PaddedSupportedCandidateWords.representativeRows_forall_length
      CarrierNodeSourceKeys.word
      (paddedCarrierSourceKeyCandidateStream descriptors)).imp
        fun _row rowLength =>
          rowLength.trans (alignedLength descriptors).symm)

end CarrierSourceKeyRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing
