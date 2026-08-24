/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowData

/-! # Retained carrier-key axis lookup data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

/-- One selected unary axis value for every carrier-key representative row. -/
def values (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (paddedCarrierKeyRepresentativeRows descriptors).words
    (CarrierKeyAxisStream.valuesWithSentinel descriptors)

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing
