/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityCompiler

/-! # Proof-free aggregate keys for compiled carrier ranks -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The six unary columns used by the carrier-rank key-equality compiler,
bundled pointwise without imposing semantic route invariants. -/
structure CarrierRankCompiledKey where
  route : Nat
  segment : Nat
  horizontalPositive : Nat
  horizontalNegative : Nat
  verticalPositive : Nat
  verticalNegative : Nat
  deriving DecidableEq

namespace CarrierRankCompiledKey

def fieldValue (field : CarrierKeyFieldProjector.Field) :
    CarrierRankCompiledKey → Nat
  | key => match field with
    | .route => key.route
    | .segment => key.segment
    | .horizontalPositive => key.horizontalPositive
    | .horizontalNegative => key.horizontalNegative
    | .verticalPositive => key.verticalPositive
    | .verticalNegative => key.verticalNegative

/-- Bundle every compiled carrier-key column at its common row index. -/
def values (descriptors : List RouteDescriptor) :
    List CarrierRankCompiledKey :=
  (List.range (CarrierRankKeyField.values .route descriptors).length).map
    fun index =>
      { route :=
          (CarrierRankKeyField.values .route descriptors).getD index 0
        segment :=
          (CarrierRankKeyField.values .segment descriptors).getD index 0
        horizontalPositive :=
          (CarrierRankKeyField.values .horizontalPositive descriptors).getD
            index 0
        horizontalNegative :=
          (CarrierRankKeyField.values .horizontalNegative descriptors).getD
            index 0
        verticalPositive :=
          (CarrierRankKeyField.values .verticalPositive descriptors).getD
            index 0
        verticalNegative :=
          (CarrierRankKeyField.values .verticalNegative descriptors).getD
            index 0 }

/-- Projecting a bundled key recovers any original compiler column. -/
@[simp] theorem values_map_fieldValue
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    (values descriptors).map (fieldValue field) =
      CarrierRankKeyField.values field descriptors := by
  cases field <;>
    simp only [values, List.map_map] <;>
    rw [CarrierRankKeyEquality.fieldValues_lengths_eq .route] <;>
    exact List.map_range_getD _ _

@[simp] theorem values_length (descriptors : List RouteDescriptor) :
    (values descriptors).length =
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length := by
  simp [values]

end CarrierRankCompiledKey
end LeanTrominoes.PeriodicOrthocrossing

end
