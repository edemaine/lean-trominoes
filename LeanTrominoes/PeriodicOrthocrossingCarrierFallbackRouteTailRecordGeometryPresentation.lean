/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordGeometryData

/-! # Filter-map presentation of selected retained-carrier geometries -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierFallbackRouteTailRecords

/-- The singleton-list presentation used by the record-block builder is the
standard sparse selected-pair projection used by rank-order semantics. -/
theorem selectedGeometries_eq_filterMap
    (entries : List CarrierFallbackTerminalData.IndexedCarrierEntry) :
    selectedGeometries entries =
      entries.flatMap fun first =>
        entries.filterMap fun second =>
          if CarrierRankOrderedPairs.retainedPredicate first second then
            some (Geometry.ofRankDatums first.1.1 second.1.1)
          else none := by
  have rowEq : ∀
      (first : CarrierFallbackTerminalData.IndexedCarrierEntry)
      (columns : List CarrierFallbackTerminalData.IndexedCarrierEntry),
      (columns.flatMap fun second =>
        if CarrierRankOrderedPairs.retainedPredicate first second then
          [{ horizontal := first.1.1.horizontal
             nextSlice := first.1.1.pairNextSlice second.1.1
             span := (second.1.1.orderCoordinate -
               first.1.1.orderCoordinate).toNat }]
        else []) =
      columns.filterMap fun second =>
        if CarrierRankOrderedPairs.retainedPredicate first second then
          some (Geometry.ofRankDatums first.1.1 second.1.1)
        else none := by
    intro first columns
    induction columns with
    | nil => rfl
    | cons second columns induction =>
        simp only [List.flatMap_cons, List.filterMap_cons]
        cases retained :
            CarrierRankOrderedPairs.retainedPredicate first second <;>
          simp [Geometry.ofRankDatums, induction]
  unfold selectedGeometries
  apply List.flatMap_congr
  intro first _firstMember
  exact rowEq first entries

end CarrierFallbackRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
