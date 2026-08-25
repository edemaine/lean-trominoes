/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCandidateExpressionData

/-! # Affine expressions for indexed crossing-segment rank fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierCrossingIndexedSegmentField

def crossingIndexedSegmentOccurrence
    (side : SegmentSide) (occurrences : Occurrence × Occurrence) : Occurrence :=
  match side with
  | .first => occurrences.1
  | .second => occurrences.2

def crossingIndexedSegmentEndpoint
    (endpoint : CarrierCrossingIndexedSegmentField.Endpoint)
    (segment : Segment) : Point :=
  match endpoint with
  | CarrierCrossingIndexedSegmentField.Endpoint.start => segment.start
  | CarrierCrossingIndexedSegmentField.Endpoint.finish => segment.finish

def occurrencePairCrossingIndexedSegmentExpression
    (field : Field) (occurrences : Occurrence × Occurrence) : Expression :=
  match field with
  | .firstSegmentIndex => ⟨occurrences.1.segmentIndex, []⟩
  | .coordinate side endpoint horizontal _ =>
      let occurrence := crossingIndexedSegmentOccurrence side occurrences
      (crossingIndexedSegmentEndpoint endpoint occurrence.segment).axisExpression
        horizontal

/-- Every boundary side of one retained crossing carries the same indexed
segment record. -/
def occurrencePairCrossingIndexedSegmentExpressionShiftBlock
    (field : Field) (occurrences : Occurrence × Occurrence)
    (_shift : Cell) : List Expression :=
  List.replicate 4
    (occurrencePairCrossingIndexedSegmentExpression field occurrences)

def occurrencePairCrossingIndexedSegmentExpressionBlock
    (field : Field) (occurrences : Occurrence × Occurrence) :
    List Expression :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingIndexedSegmentExpressionShiftBlock
      field occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierCrossingIndexedSegmentField

def crossingIndexedSegmentExpressionBlocks (field : Field) :
    List (List RouteDescriptorPairAffine.Expression) :=
  crossingSlots.map fun slot =>
    RouteDescriptorPairAffine.occurrencePairCrossingIndexedSegmentExpressionBlock
      field slot.occurrences

def crossingIndexedSegmentExpressions (field : Field) :
    List RouteDescriptorPairAffine.Expression :=
  (crossingIndexedSegmentExpressionBlocks field).flatten

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
