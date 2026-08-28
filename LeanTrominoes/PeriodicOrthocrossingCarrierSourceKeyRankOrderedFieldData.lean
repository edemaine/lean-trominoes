/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupData
import LeanTrominoes.UnaryPermutationRankBlockLookupData

/-! # Carrier source-key fields in global rank order -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRankOrderedFields

abbrev fieldCount : Nat :=
  CarrierSourceKeyRepresentativeFieldLookup.fieldCount

/-- Reorder every complete physical source-key field block by the compiled
global carrier rank column. -/
def values (descriptors : List RouteDescriptor) : List Nat :=
  UnaryPermutationRankBlockLookup.values fieldCount
    (CarrierRankGlobal.ranks descriptors)
    (CarrierSourceKeyRepresentativeFieldLookup.selectedFields descriptors)

end CarrierSourceKeyRankOrderedFields
end LeanTrominoes.PeriodicOrthocrossing
