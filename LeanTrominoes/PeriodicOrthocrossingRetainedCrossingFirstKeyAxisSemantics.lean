/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingFirstAxisSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingIndexedSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyAxisDatum

/-! # Descriptor axis value of a retained crossing's first carrier -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The first carrier of a retained crossing has descriptor-derived unary
axis value one. -/
theorem retainedCrossing_first_carrierKey_axisValue
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (descriptors : List RouteDescriptor)
    (indexedSegmentsEq :
      (drawing graph).indexedSegments =
        routeDescriptorIndexedSegments descriptors)
    {record : CrossingRecord}
    (recordMember : record ∈ retainedCrossings graph) :
    RouteDescriptorCarrierKeyAxisDatum.value descriptors
        (some (PeriodicGridDrawing.SegmentOccurrenceKey
          record.first record.firstTranslate)) =
      FixedAxisUnaryFields.value true true := by
  have member : record.first ∈
      routeDescriptorIndexedSegments descriptors := by
    rw [← indexedSegmentsEq]
    exact retainedCrossing_first_indexed_mem graph recordMember
  rw [RouteDescriptorCarrierKeyAxisDatum.value_some_segmentOccurrenceKey
    descriptors record.first record.firstTranslate member]
  have horizontal :=
    (GridSegment.isHorizontal_translate _ _).mp
      (retainedCrossing_firstHorizontal graph recordMember)
  simp [horizontal, FixedAxisUnaryFields.value]

end LeanTrominoes.PeriodicOrthocrossing
