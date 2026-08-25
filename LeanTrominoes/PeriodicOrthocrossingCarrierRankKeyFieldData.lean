/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeySemanticKeyData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Selected carrier-key fields of carrier rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

/-- One selected key-column value for every padded carrier-node slot,
followed by the rejection sentinel required by representative lookup. -/
def alignedValuesWithSentinel
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  (CarrierActiveKeyRecipeStream.semanticKeys descriptors).map
      (CarrierKeyFieldProjector.value field) ++
    [0]

/-- Look up one key column at every compact carrier-node representative. -/
def values (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    (alignedValuesWithSentinel field) descriptors

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end
