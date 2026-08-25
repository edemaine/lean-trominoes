/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumKeyFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldSemantics

/-! # Selected carrier-key fields as indexed rank-scan columns -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

/-- Every physical-key lookup is the rank-scan column named by its fixed
zero-indexed selector. -/
theorem values_eq_indexedField
    (field : CarrierKeyFieldProjector.Field)
    (period : Nat) (descriptors : List RouteDescriptor) :
    values field descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD (index field) 0) := by
  simpa only [scanUnaryFields_getD_index] using
    values_eq_selectedFieldValuesAtPeriod field period descriptors

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end
