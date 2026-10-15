/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Last.LastTrueUnaryValueLookupMachine
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Key.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowData

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
