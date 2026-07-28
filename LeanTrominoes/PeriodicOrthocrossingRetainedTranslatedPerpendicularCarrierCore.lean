import LeanTrominoes.PeriodicOrthocrossingRetainedTranslatedParallelCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierSeparation

/-!
# Retention of translated perpendicular carrier crossings

The retained crossing window is defined by the physical crossing point, not
by requiring both source-occurrence translations to be neighboring.  Thus a
proper horizontal-first crossing belongs to the retained window whenever its
point lies in the retained square.  This criterion is the bridge needed for
perpendicular periodic carrier separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Adding one common period shift preserves inequality of segment
occurrence keys. -/
theorem segmentOccurrenceKeys_ne_add
    {first second : IndexedGridSegment}
    {firstTranslate secondTranslate shift : Cell}
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate) :
    PeriodicGridDrawing.SegmentOccurrenceKey first
          (Cell.add firstTranslate shift) ≠
      PeriodicGridDrawing.SegmentOccurrenceKey second
          (Cell.add secondTranslate shift) := by
  intro translatedEqual
  apply different
  rcases firstTranslate with ⟨firstX, firstY⟩
  rcases secondTranslate with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
    Cell.add, Prod.mk.injEq] at translatedEqual ⊢
  rcases translatedEqual with
    ⟨routeEqual, segmentEqual, xEqual, yEqual⟩
  exact ⟨routeEqual, segmentEqual, by omega, by omega⟩

/-- A proper horizontal-first crossing of listed source segments is retained
whenever its crossing point lies in the retained physical square. -/
theorem crossing_mem_retained_of_proper_of_point_in_retention
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {record : CrossingRecord}
    (firstMem :
      record.first ∈ (drawing graph).indexedSegments)
    (secondMem :
      record.second ∈ (drawing graph).indexedSegments)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          record.first record.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          record.second record.secondTranslate)
    (proper :
      GridSegment.ProperlyCrossesAt
        (record.firstSegment graph)
        (record.secondSegment graph)
        record.point)
    (firstHorizontal :
      (record.firstSegment graph).IsHorizontal)
    (pointBounded :
      InCarrierCrossingRetentionSquare graph record.point) :
    record ∈ retainedCrossings graph := by
  have normalizedProper :=
    periodNormalize_properlyCrossesAt graph record proper
  have normalizedDifferent :=
    periodNormalize_occurrenceKeys_ne graph record different
  have normalizedFirstHorizontal :
      ((record.periodNormalize graph).firstSegment graph).IsHorizontal := by
    let offset :=
      (drawing graph).periodTranslation
        (crossingPeriodShift graph record)
    apply (GridSegment.isHorizontal_translate _ offset).mp
    rw [periodNormalize_firstSegment_translate graph record]
    exact firstHorizontal
  have normalizedMem :
      record.periodNormalize graph ∈ orientedCrossings graph := by
    apply (mem_orientedCrossings_iff graph _).mpr
    refine ⟨?_, normalizedFirstHorizontal⟩
    exact
      drawing_crossing_mem_canonicalCrossings
        wellFormed degree isLocal firstMem secondMem
        normalizedDifferent
        (periodNormalize_point_inFundamental graph record)
        normalizedProper.1 normalizedProper.2.1
  exact
    mem_retainedCrossings_of_periodNormalize_mem_of_shift_mem
      graph record normalizedMem
      (crossingPeriodShift_mem_retentionShifts
        graph record pointBounded)

/-- If a translated selected horizontal lens overlaps a selected vertical
lens, their horizontal-first crossing and its inverse translate both lie in
the retained crossing window. -/
theorem
    retainedCarrier_periodTranslate_crossing_and_back_mem_of_horizontal_vertical_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (firstHorizontal : firstLink.first.isHorizontal = true)
    (secondVertical : ¬secondLink.first.isHorizontal = true)
    (shift : Cell)
    (rectanglesOverlap :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph
          (carrierLinkPeriodTranslate graph firstLink shift))
        (drawingCompleteCarrierLinkRectangleUpper graph
          (carrierLinkPeriodTranslate graph firstLink shift))
        (drawingCompleteCarrierLinkRectangleLower graph secondLink)
        (drawingCompleteCarrierLinkRectangleUpper graph secondLink)) :
    let translatedFirst :=
      carrierLinkPeriodTranslate graph firstLink shift
    let crossing : CrossingRecord :=
      ⟨translatedFirst.first.indexed,
        translatedFirst.first.translate,
        secondLink.first.indexed,
        secondLink.first.translate,
        orientedIntersectionPoint
          (translatedFirst.first.supportingSegment graph)
          (secondLink.first.supportingSegment graph)⟩
    crossing ∈ retainedCrossings graph ∧
      crossing.periodTranslate graph (Cell.neg shift) ∈
        retainedCrossings graph := by
  let translatedFirst :=
    carrierLinkPeriodTranslate graph firstLink shift
  have translatedFirstFirst :
      translatedFirst.first =
        (carrierLinkPeriodTranslate graph firstLink shift).first := rfl
  let horizontalNode := translatedFirst.first
  let verticalNode := secondLink.first
  let horizontalSegment := horizontalNode.supportingSegment graph
  let verticalSegment := verticalNode.supportingSegment graph
  let point :=
    orientedIntersectionPoint horizontalSegment verticalSegment
  let crossing : CrossingRecord :=
    ⟨horizontalNode.indexed, horizontalNode.translate,
      verticalNode.indexed, verticalNode.translate, point⟩
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstIndexedMem :
      horizontalNode.indexed ∈ (drawing graph).indexedSegments := by
    simpa [horizontalNode, translatedFirst] using
      retainedCarrierNode_periodTranslate_indexed_mem
        graph firstEndpoints.1 shift
  have secondIndexedMem :
      verticalNode.indexed ∈ (drawing graph).indexedSegments := by
    simpa [verticalNode] using
      retainedCarrierNode_indexed_mem graph secondEndpoints.1
  have firstAligned :
      firstLink.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      firstLink.first.indexed
      (retainedCarrierNode_indexed_mem graph firstEndpoints.1)
  have secondAligned :
      secondLink.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      secondLink.first.indexed
      (retainedCarrierNode_indexed_mem graph secondEndpoints.1)
  have horizontal :
      horizontalSegment.IsHorizontal := by
    unfold horizontalSegment CarrierNode.supportingSegment
    apply (GridSegment.isHorizontal_translate _ _).mpr
    simpa [horizontalNode, translatedFirst] using
      (retainedCarrierNode_isHorizontal_iff
        graph firstEndpoints.1 firstAligned).mp firstHorizontal
  have vertical :
      verticalSegment.IsVertical := by
    unfold verticalSegment CarrierNode.supportingSegment
    apply (GridSegment.isVertical_translate _ _).mpr
    exact secondAligned.resolve_left fun storedHorizontal =>
      secondVertical
        ((retainedCarrierNode_isHorizontal_iff
          graph secondEndpoints.1 secondAligned).mpr storedHorizontal)
  have horizontalBounds :=
    retainedDrawingCompleteCarrierLink_periodTranslate_horizontal_support_bounded
      wellFormed degree isLocal firstMem firstHorizontal shift
  have verticalBounds :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal secondMem secondVertical
  have horizontalNormal :=
    retainedCarrierNode_periodTranslate_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1 shift
  have verticalNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  simp only [CarrierNode.isHorizontal_periodTranslate,
    firstHorizontal, if_true] at horizontalNormal
  rw [if_neg secondVertical] at verticalNormal
  simp only [planarMacroScale] at horizontalBounds verticalBounds
  simp only [planarMacroScale] at horizontalNormal verticalNormal
  have overlapData :
      ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.position graph).1 ≤
          (secondLink.first.position graph).1 + 2 ∧
        (secondLink.first.position graph).1 - 1 ≤
          ((carrierLinkPeriodTranslate graph firstLink shift).second
            |>.position graph).1 ∧
        ((carrierLinkPeriodTranslate graph firstLink shift).first
            |>.position graph).2 - 2 ≤
          (secondLink.second.position graph).2 ∧
        (secondLink.first.position graph).2 ≤
          ((carrierLinkPeriodTranslate graph firstLink shift).first
            |>.position graph).2 + 1 := by
    unfold drawingCompleteCarrierLinkRectangleLower
      drawingCompleteCarrierLinkRectangleUpper
      ClosedGridRectanglesSeparated at rectanglesOverlap
    simp only [carrierLinkPeriodTranslate_first,
      carrierLinkPeriodTranslate_second,
      CarrierNode.isHorizontal_periodTranslate,
      firstHorizontal, secondVertical, Bool.false_eq_true,
      if_true, if_false, not_or] at rectanglesOverlap
    simp only [carrierLinkPeriodTranslate_first,
      carrierLinkPeriodTranslate_second]
    omega
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second] at horizontalBounds overlapData
  have horizontalContains :
      horizontalSegment.InteriorContains point := by
    apply Or.inl
    refine ⟨horizontal, rfl, ?_⟩
    unfold GridSegment.StrictlyBetween
    simp only [point, orientedIntersectionPoint,
      horizontalSegment, verticalSegment,
      horizontalNode, verticalNode]
    rw [translatedFirstFirst]
    simp only [carrierLinkPeriodTranslate_first]
    omega
  have verticalContains :
      verticalSegment.InteriorContains point := by
    apply Or.inr
    refine ⟨vertical, rfl, ?_⟩
    unfold GridSegment.StrictlyBetween
    simp only [point, orientedIntersectionPoint,
      horizontalSegment, verticalSegment,
      horizontalNode, verticalNode]
    rw [translatedFirstFirst]
    simp only [carrierLinkPeriodTranslate_first]
    omega
  have carrierKeysDifferent :
      horizontalNode.carrierKey ≠ verticalNode.carrierKey := by
    intro keysEqual
    have fieldsEqual :=
      carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
        graph firstIndexedMem secondIndexedMem keysEqual
    have segmentsEqual :
        horizontalSegment = verticalSegment := by
      simp [horizontalSegment, verticalSegment,
        horizontalNode, verticalNode,
        CarrierNode.supportingSegment,
        fieldsEqual.1, fieldsEqual.2]
    rw [segmentsEqual] at horizontal
    exact vertical.2 horizontal.1
  have occurrenceDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey
          horizontalNode.indexed horizontalNode.translate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          verticalNode.indexed verticalNode.translate := by
    simpa [CarrierNode.carrierKey_eq_indexed_translate] using
      carrierKeysDifferent
  have proper :
      GridSegment.ProperlyCrossesAt
        horizontalSegment verticalSegment point :=
    drawing_isOrthocrossing wellFormed degree isLocal
      horizontalNode.indexed firstIndexedMem
      verticalNode.indexed secondIndexedMem
      horizontalNode.translate verticalNode.translate point
      occurrenceDifferent
      (by simpa [horizontalSegment, horizontalNode,
        CarrierNode.supportingSegment] using horizontalContains)
      (by simpa [verticalSegment, verticalNode,
        CarrierNode.supportingSegment] using verticalContains)
  have pointBounded :
      InCarrierCrossingRetentionSquare graph point :=
    drawing_neighbor_occurrence_point_in_retention_square
      wellFormed degree isLocal secondIndexedMem
      (retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph secondMem)
      (by simpa [verticalSegment, verticalNode,
        CarrierNode.supportingSegment] using verticalContains)
  have crossingFirstSegment :
      crossing.firstSegment graph = horizontalSegment := by
    simp [crossing, horizontalSegment, horizontalNode,
      CrossingRecord.firstSegment, CarrierNode.supportingSegment]
  have crossingSecondSegment :
      crossing.secondSegment graph = verticalSegment := by
    simp [crossing, verticalSegment, verticalNode,
      CrossingRecord.secondSegment, CarrierNode.supportingSegment]
  have crossingMem : crossing ∈ retainedCrossings graph := by
    apply crossing_mem_retained_of_proper_of_point_in_retention
      wellFormed degree isLocal firstIndexedMem secondIndexedMem
      occurrenceDifferent
    · rw [crossingFirstSegment, crossingSecondSegment]
      simpa [crossing, point] using proper
    · rw [crossingFirstSegment]
      exact horizontal
    · simpa [crossing, point] using pointBounded
  let backCrossing :=
    crossing.periodTranslate graph (Cell.neg shift)
  let backOffset :=
    (drawing graph).periodTranslation (Cell.neg shift)
  have backFirstMem :
      backCrossing.first ∈ (drawing graph).indexedSegments := by
    simpa [backCrossing, CrossingRecord.periodTranslate,
      crossing] using firstIndexedMem
  have backSecondMem :
      backCrossing.second ∈ (drawing graph).indexedSegments := by
    simpa [backCrossing, CrossingRecord.periodTranslate,
      crossing] using secondIndexedMem
  have backDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey
          backCrossing.first backCrossing.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          backCrossing.second backCrossing.secondTranslate := by
    simpa [backCrossing, CrossingRecord.periodTranslate] using
      segmentOccurrenceKeys_ne_add
        (shift := Cell.neg shift) occurrenceDifferent
  have backFirstContains :
      (backCrossing.firstSegment graph).InteriorContains
        backCrossing.point := by
    rw [show backCrossing.firstSegment graph =
        (crossing.firstSegment graph).translate backOffset by
      exact CrossingRecord.firstSegment_periodTranslate
        graph crossing (Cell.neg shift)]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (crossing.firstSegment graph) backOffset crossing.point).mpr
        (by
          rw [crossingFirstSegment]
          simpa [crossing, point] using horizontalContains)
  have backSecondContains :
      (backCrossing.secondSegment graph).InteriorContains
        backCrossing.point := by
    rw [show backCrossing.secondSegment graph =
        (crossing.secondSegment graph).translate backOffset by
      exact CrossingRecord.secondSegment_periodTranslate
        graph crossing (Cell.neg shift)]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (crossing.secondSegment graph) backOffset crossing.point).mpr
        (by
          rw [crossingSecondSegment]
          simpa [crossing, point] using verticalContains)
  have backFirstHorizontal :
      (backCrossing.firstSegment graph).IsHorizontal := by
    rw [show backCrossing.firstSegment graph =
        (crossing.firstSegment graph).translate backOffset by
      exact CrossingRecord.firstSegment_periodTranslate
        graph crossing (Cell.neg shift)]
    exact (GridSegment.isHorizontal_translate _ _).mpr
      (by rw [crossingFirstSegment]; exact horizontal)
  have backSecondVertical :
      (backCrossing.secondSegment graph).IsVertical := by
    rw [show backCrossing.secondSegment graph =
        (crossing.secondSegment graph).translate backOffset by
      exact CrossingRecord.secondSegment_periodTranslate
        graph crossing (Cell.neg shift)]
    exact (GridSegment.isVertical_translate _ _).mpr
      (by rw [crossingSecondSegment]; exact vertical)
  have backProper :
      GridSegment.ProperlyCrossesAt
        (backCrossing.firstSegment graph)
        (backCrossing.secondSegment graph)
        backCrossing.point :=
    ⟨backFirstContains, backSecondContains,
      Or.inl ⟨backFirstHorizontal, backSecondVertical⟩⟩
  have backFirstNeighbor :
      IsNeighborTranslation backCrossing.firstTranslate := by
    simpa [backCrossing, crossing, horizontalNode,
      translatedFirst, CrossingRecord.periodTranslate,
      CarrierNode.translate_periodTranslate,
      Cell.neg, Cell.sub, Cell.add] using
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph firstMem
  have backPointBounded :
      InCarrierCrossingRetentionSquare graph backCrossing.point :=
    drawing_neighbor_occurrence_point_in_retention_square
      wellFormed degree isLocal backFirstMem backFirstNeighbor
      backFirstContains
  have backCrossingMem :
      backCrossing ∈ retainedCrossings graph :=
    crossing_mem_retained_of_proper_of_point_in_retention
      wellFormed degree isLocal backFirstMem backSecondMem
      backDifferent backProper backFirstHorizontal backPointBounded
  exact ⟨crossingMem, backCrossingMem⟩

end PeriodicOrthocrossing
end LeanTrominoes
