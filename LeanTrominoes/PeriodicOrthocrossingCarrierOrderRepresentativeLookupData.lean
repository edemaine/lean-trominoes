/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeRowCompiler

/-! # Representative lookup data for carrier order coordinates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderRepresentativeLookup

/-- Select one positive or negative order coordinate for every retained
carrier-key representative row. -/
def values (keepPositive : Bool)
    (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (CarrierOrderRepresentativeRows.rows descriptors).words
    (CarrierOrderCandidateFieldStream.valuesWithSentinel
      keepPositive descriptors)

end CarrierOrderRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing
