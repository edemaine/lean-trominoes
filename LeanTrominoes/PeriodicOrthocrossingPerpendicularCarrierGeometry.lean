/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCarrierSeparation

/-!
# Perpendicular retained-carrier geometry

Parallel retained carrier lenses are separated by their source corridors.
For perpendicular lenses, the remaining case begins only when their narrow
physical rectangles overlap.  This file converts that physical overlap back
to the unique proper crossing of their translated source-segment occurrences
and proves that the crossing is present in the retained crossing halo.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every listed carrier node uses one of the nine retained occurrence
translations. -/
theorem carrierNode_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph) :
    IsNeighborTranslation node.translate := by
  cases node with
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at nodeMem
        simpa using nodeMem
      exact
        (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
          graph boundaryMem).2
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold drawingCarrierNodes at nodeMem
        simpa using nodeMem
      exact (drawingSegmentTerminal_indexed_mem graph terminalMem).2

/-- Perpendicular retained carrier links have different supporting occurrence
keys. -/
theorem drawingCompleteCarrierLinks_keys_ne_of_perpendicular
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem : firstLink ∈ drawingCompleteCarrierLinks graph)
    (secondMem : secondLink ∈ drawingCompleteCarrierLinks graph)
    (perpendicular :
      CarrierLinksPerpendicular firstLink secondLink) :
    firstLink.first.carrierKey ≠
      secondLink.first.carrierKey := by
  intro keyEqual
  have firstEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph secondMem
  have supportEqual :=
    carrierNode_supportingSegment_eq_of_carrierKey_eq
      firstEndpoints.1 secondEndpoints.1 keyEqual
  have firstAligned :
      firstLink.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      firstLink.first.indexed
      (carrierNode_indexed_mem graph firstEndpoints.1)
  have secondAligned :
      secondLink.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      secondLink.first.indexed
      (carrierNode_indexed_mem graph secondEndpoints.1)
  rcases perpendicular with
      ⟨firstHorizontalTag, secondVerticalTag⟩ |
      ⟨firstVerticalTag, secondHorizontalTag⟩
  · have firstHorizontal :
        (firstLink.first.supportingSegment graph).IsHorizontal := by
      exact
        (GridSegment.isHorizontal_translate _ _).mpr
          ((carrierNode_isHorizontal_iff
            graph firstEndpoints.1 firstAligned).mp
              firstHorizontalTag)
    have secondVertical :
        (secondLink.first.supportingSegment graph).IsVertical := by
      apply (GridSegment.isVertical_translate _ _).mpr
      exact secondAligned.resolve_left fun secondHorizontal =>
        secondVerticalTag
          ((carrierNode_isHorizontal_iff
            graph secondEndpoints.1 secondAligned).mpr
              secondHorizontal)
    rw [supportEqual] at firstHorizontal
    exact secondVertical.2 firstHorizontal.1
  · have firstVertical :
        (firstLink.first.supportingSegment graph).IsVertical := by
      apply (GridSegment.isVertical_translate _ _).mpr
      exact firstAligned.resolve_left fun firstHorizontal =>
        firstVerticalTag
          ((carrierNode_isHorizontal_iff
            graph firstEndpoints.1 firstAligned).mpr
              firstHorizontal)
    have secondHorizontal :
        (secondLink.first.supportingSegment graph).IsHorizontal := by
      exact
        (GridSegment.isHorizontal_translate _ _).mpr
          ((carrierNode_isHorizontal_iff
            graph secondEndpoints.1 secondAligned).mp
              secondHorizontalTag)
    rw [supportEqual] at firstVertical
    exact firstVertical.2 secondHorizontal.1

/-- If a horizontal retained lens and a vertical retained lens have
overlapping physical rectangles, their translated source occurrences cross
properly at the point selected by their fixed row and column. -/
theorem
    drawingCompleteCarrierLinks_crossing_mem_of_horizontal_vertical_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {horizontalLink verticalLink : EqualityLink CarrierNode}
    (horizontalMem :
      horizontalLink ∈ drawingCompleteCarrierLinks graph)
    (verticalMem :
      verticalLink ∈ drawingCompleteCarrierLinks graph)
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
    crossing ∈ orientedCrossingHalo graph := by
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
    drawingCompleteCarrierLink_endpoints_mem graph horizontalMem
  have verticalEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph verticalMem
  have horizontalAligned :
      horizontalNode.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      horizontalNode.indexed
      (carrierNode_indexed_mem graph horizontalEndpoints.1)
  have verticalAligned :
      verticalNode.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      verticalNode.indexed
      (carrierNode_indexed_mem graph verticalEndpoints.1)
  have horizontal :
      horizontalSegment.IsHorizontal := by
    exact
      (GridSegment.isHorizontal_translate _ _).mpr
        ((carrierNode_isHorizontal_iff
          graph horizontalEndpoints.1 horizontalAligned).mp
            horizontalTag)
  have vertical :
      verticalSegment.IsVertical := by
    apply (GridSegment.isVertical_translate _ _).mpr
    exact verticalAligned.resolve_left fun verticalHorizontal =>
      verticalTag
        ((carrierNode_isHorizontal_iff
          graph verticalEndpoints.1 verticalAligned).mpr
            verticalHorizontal)
  have horizontalBounds :=
    drawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal horizontalMem horizontalTag
  have verticalBounds :=
    drawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal verticalMem verticalTag
  have horizontalNormal :=
    carrierNode_position_normalCoordinate
      wellFormed degree isLocal horizontalEndpoints.1
  have verticalNormal :=
    carrierNode_position_normalCoordinate
      wellFormed degree isLocal verticalEndpoints.1
  rw [if_pos horizontalTag] at horizontalNormal
  rw [if_neg verticalTag] at verticalNormal
  simp only [planarMacroScale] at horizontalBounds verticalBounds horizontalNormal verticalNormal
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
    apply drawingCompleteCarrierLinks_keys_ne_of_perpendicular
      wellFormed degree isLocal horizontalMem verticalMem
    exact Or.inl ⟨horizontalTag, verticalTag⟩
  have proper :=
    drawing_isOrthocrossing wellFormed degree isLocal
      horizontalNode.indexed
      (carrierNode_indexed_mem graph horizontalEndpoints.1)
      verticalNode.indexed
      (carrierNode_indexed_mem graph verticalEndpoints.1)
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
  change crossing ∈ orientedCrossingHalo graph
  apply (mem_orientedCrossingHalo_iff graph crossing).mpr
  refine
    ⟨(mem_neighborOccurrences_iff graph _).mpr
        ⟨carrierNode_indexed_mem graph horizontalEndpoints.1,
          carrierNode_translate_neighbor graph horizontalEndpoints.1⟩,
      (mem_neighborOccurrences_iff graph _).mpr
        ⟨carrierNode_indexed_mem graph verticalEndpoints.1,
          carrierNode_translate_neighbor graph verticalEndpoints.1⟩,
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
