/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Key.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Selected horizontal field of carrier rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankHorizontalField

/-- Look up the horizontal bit at every compact carrier-node
representative. -/
def values (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    CarrierKeyAxisStream.valuesWithSentinel descriptors

end CarrierRankHorizontalField
end LeanTrominoes.PeriodicOrthocrossing
