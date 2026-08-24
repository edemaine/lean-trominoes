/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowLength
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamSentinelLength

/-! # Retained carrier-key axis lookup input -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

/-- Every compiled carrier representative row aligns with the complete
sentinel-extended carrier-axis value stream. -/
theorem representativeRows_forall_values_length
    (descriptors : List RouteDescriptor) :
    (paddedCarrierKeyRepresentativeRows descriptors).words.Forall fun row =>
      row.length =
        (CarrierKeyAxisStream.valuesWithSentinel descriptors).length := by
  unfold paddedCarrierKeyRepresentativeRows
  rw [CarrierKeyAxisStream.valuesWithSentinel_length]
  exact PaddedSupportedCandidateWords.representativeRows_forall_length
    CarrierKeyWords.word (paddedCarrierKeyCandidateStream descriptors)

/-- Promised input to the generic last-true unary lookup machine. -/
def input (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (paddedCarrierKeyRepresentativeRows descriptors).words
  values := CarrierKeyAxisStream.valuesWithSentinel descriptors
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (representativeRows_forall_values_length descriptors)

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing
