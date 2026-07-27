import LeanTrominoes.PeriodicOrthocrossingCarrierSupportGeometry
import LeanTrominoes.PeriodicOrthocrossingContinuousParallel

/-!
# Separation of parallel retained carrier corridors

Distinct horizontal source occurrences either lie on different rows or have
disjoint continuous axial interiors.  The source-corridor bounds turn both
cases into strict separation of the corresponding physical lens rectangles.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Horizontal retained links with different occurrence keys have strictly
separated lens rectangles. -/
theorem
    drawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_key_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem : firstLink ∈ drawingCompleteCarrierLinks graph)
    (secondMem : secondLink ∈ drawingCompleteCarrierLinks graph)
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
      drawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_normal_ne
        wellFormed degree isLocal
        firstMem secondMem firstHorizontal secondHorizontal normalDifferent
  · have endpointsFirst :=
      drawingCompleteCarrierLink_endpoints_mem graph firstMem
    have endpointsSecond :=
      drawingCompleteCarrierLink_endpoints_mem graph secondMem
    have firstAligned :
        firstLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        firstLink.first.indexed
        (carrierNode_indexed_mem graph endpointsFirst.1)
    have secondAligned :
        secondLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        secondLink.first.indexed
        (carrierNode_indexed_mem graph endpointsSecond.1)
    have firstStoredHorizontal :
        firstLink.first.indexed.segment.IsHorizontal :=
      (carrierNode_isHorizontal_iff
        graph endpointsFirst.1 firstAligned).mp firstHorizontal
    have secondStoredHorizontal :
        secondLink.first.indexed.segment.IsHorizontal :=
      (carrierNode_isHorizontal_iff
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
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using keyDifferent
    have noContinuousMeet :=
      drawing_horizontalContinuousInteriors_disjoint
        wellFormed degree isLocal
        (carrierNode_indexed_mem graph endpointsFirst.1)
        (carrierNode_indexed_mem graph endpointsSecond.1)
        firstSupportHorizontal secondSupportHorizontal occurrenceDifferent
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
      drawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_support_disjoint
        wellFormed degree isLocal
        firstMem secondMem firstHorizontal secondHorizontal axialDisjoint

end PeriodicOrthocrossing
end LeanTrominoes
