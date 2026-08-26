/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalData
import LeanTrominoes.UnaryPermutationRankLookupData

/-! # Carrier rank-datum fields in global-rank order -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

/-- Reorder one compiled carrier datum field by its global key-major rank. -/
def Field.rankOrderedValues (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  UnaryPermutationRankLookup.values
    (CarrierRankGlobal.ranks descriptors) (field.values descriptors)

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
