/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData

/-! # Rank semantics of source-key crossing-record fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

@[simp] theorem rankValue_carrierNodeRankDatumAtPeriod
    (field : Field) (period : Nat) (node : CarrierNode) :
    rankValue field (carrierNodeRankDatumAtPeriod period node) =
      nodeValue field node := by
  cases node with
  | terminal terminal => rfl
  | boundary boundary =>
      cases field <;>
        simp [rankValue, recordKey, nodeValue, sourceNodeValue,
          sourceKey, component, keyField, CarrierNodeSourceKeys.pair,
          CarrierNodeSourceKeys.firstCrossingKey,
          CarrierNodeSourceKeys.secondCrossingKey,
          CarrierNodeSourceKeys.taggedKey,
          PeriodicGridDrawing.SegmentOccurrenceKey,
          CrossingRecord.code, indexedGridSegmentCode,
          CarrierKeyFieldProjector.keyValue,
          carrierNodeRankDatumAtPeriod]

@[simp] theorem fieldValueAtPeriod_rankValue_map_code
    (field : Field) (period : Nat) (node : Option CarrierNode) :
    CarrierRankDatumLookup.fieldValueAtPeriod period (rankValue field)
        (node.map CarrierNode.code) =
      optionalNodeValue field node := by
  cases node with
  | none => rfl
  | some node =>
      simp [CarrierRankDatumLookup.fieldValueAtPeriod, optionalNodeValue]

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing
