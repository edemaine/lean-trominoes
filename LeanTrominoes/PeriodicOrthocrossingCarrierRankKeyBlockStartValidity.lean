/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyBlockStartAlignment

/-! # Alignment validity for carrier-key block-start lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyBlockStartValidity

opaque valid (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.RowsValid
      (CarrierRankKeyContributionStarts.starts descriptors)
      (CarrierRankKeyEqualityRows.semanticRows descriptors) :=
  LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (CarrierRankKeyBlockStartAlignment.semanticRows_forall_starts_length
      descriptors)

end CarrierRankKeyBlockStartValidity
end LeanTrominoes.PeriodicOrthocrossing
