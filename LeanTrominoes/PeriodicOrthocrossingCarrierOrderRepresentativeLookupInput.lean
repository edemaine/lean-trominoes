/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeRowLength

/-! # Valid lookup inputs for carrier order coordinates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderRepresentativeLookup

/-- Package representative rows with their aligned positive or negative
order-coordinate values as promised input to the generic lookup machine. -/
def input (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (CarrierOrderRepresentativeRows.rows descriptors).words
  values := CarrierOrderCandidateFieldStream.valuesWithSentinel
    keepPositive descriptors
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (CarrierOrderRepresentativeRows.rows_forall_values_length
      keepPositive descriptors)

end CarrierOrderRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing
