/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierCore

/-!
# Overlap geometry of selected retained perpendicular carriers

If a horizontal and a vertical selected retained lens have overlapping narrow
rectangles, their neighboring translated source occurrences cross properly at
the row/column intersection.  The exact horizontal-first record belongs to
the retained crossing orbit.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Overlapping horizontal and vertical selected retained lenses determine an
exact crossing in the retained crossing orbit. -/
theorem
    retainedDrawingCompleteCarrierLinks_crossing_mem_of_horizontal_vertical_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {horizontalLink verticalLink : EqualityLink CarrierNode}
    (horizontalMem :
      horizontalLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (verticalMem :
      verticalLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontalTag :
      horizontalLink.first.isHorizontal = true)
    (verticalTag :
      ¬verticalLink.first.isHorizontal = true)
    (rectanglesOverlap :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph horizontalLink)
        (drawingCompleteCarrierLinkRectangleUpper graph horizontalLink)
        (drawingCompleteCarrierLinkRectangleLower graph verticalLink)
        (drawingCompleteCarrierLinkRectangleUpper graph verticalLink)) :
    let crossing : CrossingRecord :=
      ⟨horizontalLink.first.indexed,
        horizontalLink.first.translate,
        verticalLink.first.indexed,
        verticalLink.first.translate,
        orientedIntersectionPoint
          (horizontalLink.first.supportingSegment graph)
          (verticalLink.first.supportingSegment graph)⟩
    crossing ∈ retainedCrossings graph := by
  let horizontalNode := horizontalLink.first
  let verticalNode := verticalLink.first
  let horizontalSegment := horizontalNode.supportingSegment graph
  let verticalSegment := verticalNode.supportingSegment graph
  let point :=
    orientedIntersectionPoint horizontalSegment verticalSegment
  let crossing : CrossingRecord :=
    ⟨horizontalNode.indexed, horizontalNode.translate,
      verticalNode.indexed, verticalNode.translate, point⟩
  have horizontalEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      graph horizontalMem
  have verticalEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      graph verticalMem
  have horizontalAligned :
      horizontalNode.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      horizontalNode.indexed
      (retainedCarrierNode_indexed_mem graph horizontalEndpoints.1)
  have verticalAligned :
      verticalNode.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      verticalNode.indexed
      (retainedCarrierNode_indexed_mem graph verticalEndpoints.1)
  have horizontal :
      horizontalSegment.IsHorizontal := by
    exact
      (GridSegment.isHorizontal_translate _ _).mpr
        ((retainedCarrierNode_isHorizontal_iff
          graph horizontalEndpoints.1 horizontalAligned).mp
            horizontalTag)
  have vertical :
      verticalSegment.IsVertical := by
    apply (GridSegment.isVertical_translate _ _).mpr
    exact verticalAligned.resolve_left fun verticalHorizontal =>
      verticalTag
        ((retainedCarrierNode_isHorizontal_iff
          graph verticalEndpoints.1 verticalAligned).mpr
            verticalHorizontal)
  have horizontalBounds :=
    retainedDrawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal horizontalMem horizontalTag
  have verticalBounds :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal verticalMem verticalTag
  have horizontalNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal horizontalEndpoints.1
  have verticalNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal verticalEndpoints.1
  rw [if_pos horizontalTag] at horizontalNormal
  rw [if_neg verticalTag] at verticalNormal
  simp only [planarMacroScale] at horizontalBounds
  simp only [planarMacroScale] at verticalBounds
  simp only [planarMacroScale] at horizontalNormal
  simp only [planarMacroScale] at verticalNormal
  have overlapData :
      (horizontalLink.first.position graph).1 ≤
          (verticalLink.first.position graph).1 + 2 ∧
        (verticalLink.first.position graph).1 - 1 ≤
          (horizontalLink.second.position graph).1 ∧
        (horizontalLink.first.position graph).2 - 2 ≤
          (verticalLink.second.position graph).2 ∧
        (verticalLink.first.position graph).2 ≤
          (horizontalLink.first.position graph).2 + 1 := by
    unfold drawingCompleteCarrierLinkRectangleLower
      drawingCompleteCarrierLinkRectangleUpper
      ClosedGridRectanglesSeparated at rectanglesOverlap
    simp only [horizontalTag, verticalTag, Bool.false_eq_true,
      if_true, if_false, not_or] at rectanglesOverlap
    omega
  have horizontalContains :
      horizontalSegment.InteriorContains point := by
    apply Or.inl
    refine ⟨horizontal, rfl, ?_⟩
    unfold GridSegment.StrictlyBetween
    simp only [point, orientedIntersectionPoint,
      horizontalSegment, verticalSegment,
      horizontalNode, verticalNode]
    omega
  have verticalContains :
      verticalSegment.InteriorContains point := by
    apply Or.inr
    refine ⟨vertical, rfl, ?_⟩
    unfold GridSegment.StrictlyBetween
    simp only [point, orientedIntersectionPoint,
      horizontalSegment, verticalSegment,
      horizontalNode, verticalNode]
    omega
  have keyDifferent :
      horizontalNode.carrierKey ≠ verticalNode.carrierKey := by
    apply retainedDrawingCompleteCarrierLinks_keys_ne_of_perpendicular
      wellFormed degree isLocal horizontalMem verticalMem
    exact Or.inl ⟨horizontalTag, verticalTag⟩
  have proper :=
    drawing_isOrthocrossing wellFormed degree isLocal
      horizontalNode.indexed
      (retainedCarrierNode_indexed_mem graph horizontalEndpoints.1)
      verticalNode.indexed
      (retainedCarrierNode_indexed_mem graph verticalEndpoints.1)
      horizontalNode.translate verticalNode.translate point
      (by
        simpa [CarrierNode.carrierKey_eq_indexed_translate] using
          keyDifferent)
      (by
        simpa [horizontalSegment, horizontalNode,
          CarrierNode.supportingSegment] using horizontalContains)
      (by
        simpa [verticalSegment, verticalNode,
          CarrierNode.supportingSegment] using verticalContains)
  change crossing ∈ retainedCrossings graph
  apply orientedCrossingHalo_subset_retainedCrossings
    wellFormed degree isLocal
  apply (mem_orientedCrossingHalo_iff graph crossing).mpr
  refine
    ⟨(mem_neighborOccurrences_iff graph _).mpr
        ⟨retainedCarrierNode_indexed_mem
            graph horizontalEndpoints.1,
          retainedDrawingCompleteCarrierLink_first_translate_neighbor
            graph horizontalMem⟩,
      (mem_neighborOccurrences_iff graph _).mpr
        ⟨retainedCarrierNode_indexed_mem
            graph verticalEndpoints.1,
          retainedDrawingCompleteCarrierLink_first_translate_neighbor
            graph verticalMem⟩,
      rfl, ?_⟩
  exact
    ⟨by
        simpa [crossing, horizontalNode, verticalNode,
          CarrierNode.carrierKey_eq_indexed_translate] using
            keyDifferent,
      by
        simpa [crossing, horizontalNode, horizontalSegment,
          CarrierNode.supportingSegment,
          CrossingRecord.firstSegment] using horizontal,
      by
        simpa [crossing, verticalNode, verticalSegment,
          CarrierNode.supportingSegment,
          CrossingRecord.secondSegment] using vertical,
      by
        simpa [crossing, horizontalNode, verticalNode,
          horizontalSegment, verticalSegment,
          CarrierNode.supportingSegment,
          CrossingRecord.firstSegment,
          CrossingRecord.secondSegment] using proper⟩

end PeriodicOrthocrossing
end LeanTrominoes
