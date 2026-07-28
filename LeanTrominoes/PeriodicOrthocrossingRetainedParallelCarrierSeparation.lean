import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierSupportGeometry
import LeanTrominoes.PeriodicOrthocrossingContinuousParallel

/-!
# Separation of selected retained parallel carriers

Distinct parallel source occurrences either use different support lines or
have disjoint continuous axial interiors.  The retained source-corridor bounds
turn both cases into strict separation of their lens rectangles.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Horizontal selected links with different occurrence keys have strictly
separated lens rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_key_ne
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
    (secondHorizontal : secondLink.first.isHorizontal = true)
    (keyDifferent :
      firstLink.first.carrierKey ≠ secondLink.first.carrierKey) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  by_cases normalDifferent :
      (firstLink.first.supportingSegment graph).start.2 ≠
        (secondLink.first.supportingSegment graph).start.2
  · exact
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_normal_ne
        wellFormed degree isLocal firstMem secondMem
        firstHorizontal secondHorizontal normalDifferent
  · have endpointsFirst :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
    have endpointsSecond :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
    have firstAligned :
        firstLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        firstLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsFirst.1)
    have secondAligned :
        secondLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        secondLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
    have firstStoredHorizontal :
        firstLink.first.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph endpointsFirst.1 firstAligned).mp firstHorizontal
    have secondStoredHorizontal :
        secondLink.first.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph endpointsSecond.1 secondAligned).mp secondHorizontal
    have firstSupportHorizontal :
        (firstLink.first.supportingSegment graph).IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr firstStoredHorizontal
    have secondSupportHorizontal :
        (secondLink.first.supportingSegment graph).IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr secondStoredHorizontal
    have occurrenceDifferent :
        PeriodicGridDrawing.SegmentOccurrenceKey
            firstLink.first.indexed firstLink.first.translate ≠
          PeriodicGridDrawing.SegmentOccurrenceKey
            secondLink.first.indexed secondLink.first.translate := by
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using
        keyDifferent
    have noContinuousMeet :=
      drawing_horizontalContinuousInteriors_disjoint
        wellFormed degree isLocal
        (retainedCarrierNode_indexed_mem graph endpointsFirst.1)
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
        firstSupportHorizontal secondSupportHorizontal
        occurrenceDifferent
    have axialDisjoint :
        ¬GridSegment.OpenIntervalsOverlap
          (firstLink.first.supportingSegment graph).start.1
          (firstLink.first.supportingSegment graph).finish.1
          (secondLink.first.supportingSegment graph).start.1
          (secondLink.first.supportingSegment graph).finish.1 := by
      intro overlap
      apply noContinuousMeet
      exact Or.inl
        ⟨firstSupportHorizontal, secondSupportHorizontal,
          not_ne_iff.mp normalDifferent, overlap⟩
    exact
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_support_disjoint
        wellFormed degree isLocal firstMem secondMem
        firstHorizontal secondHorizontal axialDisjoint

/-- Vertical selected links with different occurrence keys have strictly
separated lens rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_vertical_key_ne
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
    (firstVertical : ¬firstLink.first.isHorizontal = true)
    (secondVertical : ¬secondLink.first.isHorizontal = true)
    (keyDifferent :
      firstLink.first.carrierKey ≠ secondLink.first.carrierKey) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  by_cases normalDifferent :
      (firstLink.first.supportingSegment graph).start.1 ≠
        (secondLink.first.supportingSegment graph).start.1
  · exact
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_vertical_normal_ne
        wellFormed degree isLocal firstMem secondMem
        firstVertical secondVertical normalDifferent
  · have endpointsFirst :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
    have endpointsSecond :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
    have firstAligned :
        firstLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        firstLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsFirst.1)
    have secondAligned :
        secondLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        secondLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
    have firstNotHorizontal :
        ¬firstLink.first.indexed.segment.IsHorizontal := by
      intro horizontal
      exact firstVertical
        ((retainedCarrierNode_isHorizontal_iff
          graph endpointsFirst.1 firstAligned).mpr horizontal)
    have secondNotHorizontal :
        ¬secondLink.first.indexed.segment.IsHorizontal := by
      intro horizontal
      exact secondVertical
        ((retainedCarrierNode_isHorizontal_iff
          graph endpointsSecond.1 secondAligned).mpr horizontal)
    have firstStoredVertical :
        firstLink.first.indexed.segment.IsVertical :=
      firstAligned.resolve_left firstNotHorizontal
    have secondStoredVertical :
        secondLink.first.indexed.segment.IsVertical :=
      secondAligned.resolve_left secondNotHorizontal
    have firstSupportVertical :
        (firstLink.first.supportingSegment graph).IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr firstStoredVertical
    have secondSupportVertical :
        (secondLink.first.supportingSegment graph).IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr secondStoredVertical
    have occurrenceDifferent :
        PeriodicGridDrawing.SegmentOccurrenceKey
            firstLink.first.indexed firstLink.first.translate ≠
          PeriodicGridDrawing.SegmentOccurrenceKey
            secondLink.first.indexed secondLink.first.translate := by
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using
        keyDifferent
    have noContinuousMeet :=
      drawing_verticalContinuousInteriors_disjoint
        wellFormed degree isLocal
        (retainedCarrierNode_indexed_mem graph endpointsFirst.1)
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
        firstSupportVertical secondSupportVertical
        occurrenceDifferent
    have axialDisjoint :
        ¬GridSegment.OpenIntervalsOverlap
          (firstLink.first.supportingSegment graph).start.2
          (firstLink.first.supportingSegment graph).finish.2
          (secondLink.first.supportingSegment graph).start.2
          (secondLink.first.supportingSegment graph).finish.2 := by
      intro overlap
      apply noContinuousMeet
      exact Or.inr
        (Or.inl
          ⟨firstSupportVertical, secondSupportVertical,
            not_ne_iff.mp normalDifferent, overlap⟩)
    exact
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_vertical_support_disjoint
        wellFormed degree isLocal firstMem secondMem
        firstVertical secondVertical axialDisjoint

end PeriodicOrthocrossing
end LeanTrominoes
