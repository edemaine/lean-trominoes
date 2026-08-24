/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingFirstKeyAxisSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingSecondKeyAxisSemantics

/-! # Descriptor-derived axes of retained crossing boundaries -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A descriptor stream reconstructing the drawing assigns every retained
crossing boundary's carrier key the zero-or-one value of that boundary's
physical axis. -/
theorem retainedBoundary_carrierKey_axisValue
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (descriptors : List RouteDescriptor)
    (indexedSegmentsEq :
      (drawing graph).indexedSegments =
        routeDescriptorIndexedSegments descriptors)
    {boundary : CrossingBoundary}
    (boundaryMember : boundary ∈ retainedCrossingBoundaries graph) :
    RouteDescriptorCarrierKeyAxisDatum.value descriptors
        (some boundary.carrierKey) =
      FixedAxisUnaryFields.value true
        (CarrierNode.boundary boundary).isHorizontal := by
  have crossingMember :=
    retainedCrossingBoundary_crossing_mem graph boundaryMember
  rcases boundary with ⟨record, side⟩
  cases side with
  | left =>
      change RouteDescriptorCarrierKeyAxisDatum.value descriptors
          (some (PeriodicGridDrawing.SegmentOccurrenceKey
            record.first record.firstTranslate)) =
        FixedAxisUnaryFields.value true true
      exact retainedCrossing_first_carrierKey_axisValue
        graph descriptors indexedSegmentsEq crossingMember
  | right =>
      change RouteDescriptorCarrierKeyAxisDatum.value descriptors
          (some (PeriodicGridDrawing.SegmentOccurrenceKey
            record.first record.firstTranslate)) =
        FixedAxisUnaryFields.value true true
      exact retainedCrossing_first_carrierKey_axisValue
        graph descriptors indexedSegmentsEq crossingMember
  | top =>
      change RouteDescriptorCarrierKeyAxisDatum.value descriptors
          (some (PeriodicGridDrawing.SegmentOccurrenceKey
            record.second record.secondTranslate)) =
        FixedAxisUnaryFields.value true false
      exact retainedCrossing_second_carrierKey_axisValue
        graph descriptors indexedSegmentsEq crossingMember
  | bottom =>
      change RouteDescriptorCarrierKeyAxisDatum.value descriptors
          (some (PeriodicGridDrawing.SegmentOccurrenceKey
            record.second record.secondTranslate)) =
        FixedAxisUnaryFields.value true false
      exact retainedCrossing_second_carrierKey_axisValue
        graph descriptors indexedSegmentsEq crossingMember

end LeanTrominoes.PeriodicOrthocrossing
