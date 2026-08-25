/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupData

/-! # Selected signed order-coordinate fields of carrier rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderField

/-- Look up one signed unary magnitude at every source-identity
representative. -/
def values (keepPositive : Bool)
    (descriptors : List RouteDescriptor) : List Nat :=
  CarrierOrderRepresentativeLookup.values keepPositive descriptors

end CarrierRankOrderField
end LeanTrominoes.PeriodicOrthocrossing
