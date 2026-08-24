/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingSecondAxisSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingIndexedSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyAxisDatum

/-! # Descriptor axis value of a retained crossing's second carrier -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The second carrier of a retained crossing has descriptor-derived unary
axis value zero. -/
theorem retainedCrossing_second_carrierKey_axisValue
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
          record.second record.secondTranslate)) =
      FixedAxisUnaryFields.value true false := by
  have member : record.second ∈
      routeDescriptorIndexedSegments descriptors := by
    rw [← indexedSegmentsEq]
    exact retainedCrossing_second_indexed_mem graph recordMember
  rw [RouteDescriptorCarrierKeyAxisDatum.value_some_segmentOccurrenceKey
    descriptors record.second record.secondTranslate member]
  have vertical :=
    (GridSegment.isVertical_translate _ _).mp
      (retainedCrossing_secondVertical graph recordMember)
  have notHorizontal : ¬record.second.segment.IsHorizontal :=
    fun horizontal => vertical.2 horizontal.1
  simp [notHorizontal, FixedAxisUnaryFields.value]

end LeanTrominoes.PeriodicOrthocrossing
