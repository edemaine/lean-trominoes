/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalSuccessorData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldLength

/-! # Length alignment of compiled carrier rank-datum fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

private theorem sourceLookupValues_length
    (alignedValues : List RouteDescriptor → List Nat)
    (descriptors : List RouteDescriptor) :
    (CarrierSourceKeyRepresentativeLookup.values
        alignedValues descriptors).length =
      (CarrierRankGlobal.ranks descriptors).length := by
  unfold CarrierSourceKeyRepresentativeLookup.values
    LastTrueUnaryValueLookupMachine.lookups
  simp only [List.length_map]
  rw [CarrierRankGlobalSuccessor.ranks_length]
  rfl

/-- Every compiled field is aligned with the global rank column on arbitrary
descriptor inputs. -/
theorem Field.values_length_eq_ranks (field : Field)
    (descriptors : List RouteDescriptor) :
    (field.values descriptors).length =
      (CarrierRankGlobal.ranks descriptors).length := by
  cases field <;>
    simp only [Field.values, CarrierRankKeyRouteField.values,
      CarrierRankKeySegmentField.values,
      CarrierRankKeySignedFields.horizontalPositiveValues,
      CarrierRankKeySignedFields.horizontalNegativeValues,
      CarrierRankKeySignedFields.verticalPositiveValues,
      CarrierRankKeySignedFields.verticalNegativeValues,
      CarrierRankKeyField.values, CarrierRankHorizontalField.values,
      CarrierNormalizationOffsetField.values,
      CarrierBoundaryPresenceField.values,
      CarrierCrossingRecordSourceField.values,
      CarrierCrossingIndexedSegmentField.values,
      CarrierCrossingPointField.values,
      CarrierOwnershipShiftField.values,
      sourceLookupValues_length]
  case orderPositive =>
    rw [CarrierRankOrderField.values_length_eq_keyValues true .route]
    exact sourceLookupValues_length _ _
  case orderNegative =>
    rw [CarrierRankOrderField.values_length_eq_keyValues false .route]
    exact sourceLookupValues_length _ _

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
