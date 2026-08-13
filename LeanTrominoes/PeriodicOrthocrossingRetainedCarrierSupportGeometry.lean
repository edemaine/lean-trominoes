/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedSameCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingCarrierSupportGeometry

/-!
# Source support of selected retained carrier corridors

Retained halo boundaries lie strictly inside their translated source
segments, while terminals retain the legacy endpoint bound.  Thus every
selected link stays within the narrow physical corridor of its source
occurrence, including halo-only carrier nodes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Every retained carrier port has axial local coordinate between one and
eleven. -/
theorem retainedCarrierNode_localPosition_axis_bounds
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    if node.isHorizontal then
      1 ≤ node.localPosition.1 ∧ node.localPosition.1 ≤ 11
    else
      1 ≤ node.localPosition.2 ∧ node.localPosition.2 ≤ 11 := by
  have axisData :=
    retainedCarrierNode_localPosition_axis_data
      graph nodeMem axisAligned
  have macrocellBounds :
      0 < node.localPosition.1 ∧ node.localPosition.1 < planarMacroScale ∧
        0 < node.localPosition.2 ∧
          node.localPosition.2 < planarMacroScale := by
    cases node with
    | boundary boundary =>
        cases boundary with
        | mk crossing side =>
            cases side <;>
              norm_num [CarrierNode.localPosition,
                CrossingSide.localPosition,
                CrossoverVariable.position, planarMacroScale]
    | terminal terminal =>
        exact
          segmentTerminalLocalPosition_in_macrocell
            terminal.indexed.segment terminal.endpoint
  by_cases horizontal : node.isHorizontal = true
  · rw [if_pos horizontal] at axisData ⊢
    simp only [planarMacroScale] at macrocellBounds
    omega
  · rw [if_neg horizontal] at axisData ⊢
    simp only [planarMacroScale] at macrocellBounds
    omega

/-- Every retained carrier node lies in the closed physical source corridor
between its two inward-facing terminal ports. -/
theorem retainedCarrierNode_orderCoordinate_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph) :
    node.supportLowerCoordinate graph ≤ node.orderCoordinate graph ∧
      node.orderCoordinate graph ≤ node.supportUpperCoordinate graph := by
  have aligned :
      node.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      node.indexed
      (retainedCarrierNode_indexed_mem graph nodeMem)
  cases node with
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      apply carrierNode_orderCoordinate_support_bounded
        wellFormed degree isLocal
      unfold drawingCarrierNodes
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨terminal, terminalMem, rfl⟩)
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      have interior :
          (CarrierNode.boundary boundary).supportingSegment graph
              |>.InteriorContains
                ((CarrierNode.boundary boundary).drawingPoint graph) := by
        simpa [CarrierNode.supportingSegment, CarrierNode.indexed,
          CarrierNode.translate, CarrierNode.drawingPoint] using
          (retainedCrossingBoundary_indexed_mem_and_contains
            graph boundaryMem).2
      have localBounds :=
        retainedCarrierNode_localPosition_axis_bounds
          (graph := graph) nodeMem aligned
      by_cases horizontalTag :
          (CarrierNode.boundary boundary).isHorizontal = true
      · rw [if_pos horizontalTag] at localBounds
        have horizontal :
            ((CarrierNode.boundary boundary).supportingSegment graph
              ).IsHorizontal := by
          exact
            (GridSegment.isHorizontal_translate _ _).mpr
              ((retainedCarrierNode_isHorizontal_iff
                graph nodeMem aligned).mp horizontalTag)
        rcases interior with onHorizontal | onVertical
        · rw [CarrierNode.supportLowerCoordinate,
            CarrierNode.supportUpperCoordinate]
          simp only [horizontalTag, if_true,
            CarrierNode.orderCoordinate]
          rw [CarrierNode.position_eq_scale_add_local]
          simp only [Cell.add, Cell.scale, planarMacroScale]
          unfold GridSegment.StrictlyBetween at onHorizontal
          rcases onHorizontal.2.2 with forward | backward
          · rw [min_eq_left (by omega), max_eq_right (by omega)]
            omega
          · rw [min_eq_right (by omega), max_eq_left (by omega)]
            omega
        · exact False.elim (horizontal.2 onVertical.1.1)
      · rw [if_neg horizontalTag] at localBounds
        have notHorizontal :
            ¬(CarrierNode.boundary boundary).indexed.segment.IsHorizontal := by
          intro horizontal
          exact horizontalTag
            ((retainedCarrierNode_isHorizontal_iff
              graph nodeMem aligned).mpr horizontal)
        have vertical :
            ((CarrierNode.boundary boundary).supportingSegment graph
              ).IsVertical := by
          exact
            (GridSegment.isVertical_translate _ _).mpr
              (aligned.resolve_left notHorizontal)
        rcases interior with onHorizontal | onVertical
        · exact False.elim (vertical.2 onHorizontal.1.1)
        · rw [CarrierNode.supportLowerCoordinate,
            CarrierNode.supportUpperCoordinate]
          simp only [horizontalTag, Bool.false_eq_true, if_false,
            CarrierNode.orderCoordinate]
          rw [CarrierNode.position_eq_scale_add_local]
          simp only [Cell.add, Cell.scale, planarMacroScale]
          unfold GridSegment.StrictlyBetween at onVertical
          rcases onVertical.2.2 with forward | backward
          · rw [min_eq_left (by omega), max_eq_right (by omega)]
            omega
          · rw [min_eq_right (by omega), max_eq_left (by omega)]
            omega

/-- Equal retained carrier keys identify one translated supporting segment. -/
theorem retainedCarrierNode_supportingSegment_eq_of_carrierKey_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey) :
    first.supportingSegment graph = second.supportingSegment graph := by
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph firstMem)
      (retainedCarrierNode_indexed_mem graph secondMem)
      keyEqual
  simp [CarrierNode.supportingSegment,
    occurrenceEqual.1, occurrenceEqual.2]

/-- A horizontal raw retained link stays within its source occurrence's
axial corridor. -/
theorem retainedDrawingCompleteCarrierLinkRaw_horizontal_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (horizontal : link.first.isHorizontal = true) :
    planarMacroScale *
          min (link.first.supportingSegment graph).start.1
            (link.first.supportingSegment graph).finish.1 +
        11 ≤
      (link.first.position graph).1 ∧
    (link.second.position graph).1 ≤
      planarMacroScale *
          max (link.first.supportingSegment graph).start.1
            (link.first.supportingSegment graph).finish.1 +
        1 := by
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have commonKey :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph linkMem
  have supportEqual :=
    retainedCarrierNode_supportingSegment_eq_of_carrierKey_eq
      endpoints.1 endpoints.2 commonKey
  have secondHorizontal :=
    (retainedDrawingCompleteCarrierLinkRaw_first_isHorizontal_iff_second
      wellFormed degree isLocal linkMem).mp horizontal
  have firstBounds :=
    retainedCarrierNode_orderCoordinate_support_bounded
      wellFormed degree isLocal endpoints.1
  have secondBounds :=
    retainedCarrierNode_orderCoordinate_support_bounded
      wellFormed degree isLocal endpoints.2
  constructor
  · simpa [CarrierNode.supportLowerCoordinate,
      CarrierNode.orderCoordinate, horizontal] using firstBounds.1
  · simpa [CarrierNode.supportUpperCoordinate,
      CarrierNode.orderCoordinate, secondHorizontal,
      ← supportEqual] using secondBounds.2

/-- The horizontal support bound for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_horizontal_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontal : link.first.isHorizontal = true) :
    planarMacroScale *
          min (link.first.supportingSegment graph).start.1
            (link.first.supportingSegment graph).finish.1 +
        11 ≤
      (link.first.position graph).1 ∧
    (link.second.position graph).1 ≤
      planarMacroScale *
          max (link.first.supportingSegment graph).start.1
            (link.first.supportingSegment graph).finish.1 +
        1 :=
  retainedDrawingCompleteCarrierLinkRaw_horizontal_support_bounded
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 horizontal

/-- A vertical raw retained link stays within its source occurrence's axial
corridor. -/
theorem retainedDrawingCompleteCarrierLinkRaw_vertical_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (vertical : ¬link.first.isHorizontal = true) :
    planarMacroScale *
          min (link.first.supportingSegment graph).start.2
            (link.first.supportingSegment graph).finish.2 +
        11 ≤
      (link.first.position graph).2 ∧
    (link.second.position graph).2 ≤
      planarMacroScale *
          max (link.first.supportingSegment graph).start.2
            (link.first.supportingSegment graph).finish.2 +
        1 := by
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have commonKey :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph linkMem
  have supportEqual :=
    retainedCarrierNode_supportingSegment_eq_of_carrierKey_eq
      endpoints.1 endpoints.2 commonKey
  have secondVertical :
      ¬link.second.isHorizontal = true := by
    exact fun secondHorizontal =>
      vertical
        ((retainedDrawingCompleteCarrierLinkRaw_first_isHorizontal_iff_second
          wellFormed degree isLocal linkMem).mpr secondHorizontal)
  have firstBounds :=
    retainedCarrierNode_orderCoordinate_support_bounded
      wellFormed degree isLocal endpoints.1
  have secondBounds :=
    retainedCarrierNode_orderCoordinate_support_bounded
      wellFormed degree isLocal endpoints.2
  constructor
  · simpa [CarrierNode.supportLowerCoordinate,
      CarrierNode.orderCoordinate, vertical] using firstBounds.1
  · simpa [CarrierNode.supportUpperCoordinate,
      CarrierNode.orderCoordinate, secondVertical,
      ← supportEqual] using secondBounds.2

/-- The vertical support bound for selected representatives. -/
theorem retainedDrawingCompleteCarrierLink_vertical_support_bounded
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (vertical : ¬link.first.isHorizontal = true) :
    planarMacroScale *
          min (link.first.supportingSegment graph).start.2
            (link.first.supportingSegment graph).finish.2 +
        11 ≤
      (link.first.position graph).2 ∧
    (link.second.position graph).2 ≤
      planarMacroScale *
          max (link.first.supportingSegment graph).start.2
            (link.first.supportingSegment graph).finish.2 +
        1 :=
  retainedDrawingCompleteCarrierLinkRaw_vertical_support_bounded
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1 vertical

/-- A retained node's physical normal coordinate is its translated source
line scaled by twenty and shifted by six. -/
theorem retainedCarrierNode_position_normalCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph) :
    if node.isHorizontal then
      (node.position graph).2 =
        planarMacroScale * (node.supportingSegment graph).start.2 + 6
    else
      (node.position graph).1 =
        planarMacroScale * (node.supportingSegment graph).start.1 + 6 := by
  have aligned :
      node.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      node.indexed
      (retainedCarrierNode_indexed_mem graph nodeMem)
  have contains :=
    retainedCarrierNode_drawingPoint_contains graph nodeMem aligned
  have localData :=
    retainedCarrierNode_localPosition_axis_data graph nodeMem aligned
  by_cases horizontalTag : node.isHorizontal = true
  · rw [if_pos horizontalTag] at localData ⊢
    have horizontal :
        node.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph nodeMem aligned).mp horizontalTag
    have supportingHorizontal :
        (node.supportingSegment graph).IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr horizontal
    have drawingY :
        (node.drawingPoint graph).2 =
          (node.supportingSegment graph).start.2 := by
      rcases contains with onHorizontal | onVertical
      · exact onHorizontal.2.1
      · exact False.elim
          (onVertical.1.2 supportingHorizontal.1)
    rw [CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega
  · rw [if_neg horizontalTag] at localData ⊢
    have notHorizontal :
        ¬node.indexed.segment.IsHorizontal := by
      intro horizontal
      exact horizontalTag
        ((retainedCarrierNode_isHorizontal_iff
          graph nodeMem aligned).mpr horizontal)
    have vertical :
        node.indexed.segment.IsVertical :=
      aligned.resolve_left notHorizontal
    have supportingVertical :
        (node.supportingSegment graph).IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr vertical
    have drawingX :
        (node.drawingPoint graph).1 =
          (node.supportingSegment graph).start.1 := by
      rcases contains with onHorizontal | onVertical
      · exact False.elim
          (supportingVertical.2 onHorizontal.1.1)
      · exact onVertical.2.1
    rw [CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega

/-- Horizontal selected links whose source intervals have disjoint open
interiors have strictly separated physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_support_disjoint
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
    (disjoint :
      ¬GridSegment.OpenIntervalsOverlap
        (firstLink.first.supportingSegment graph).start.1
        (firstLink.first.supportingSegment graph).finish.1
        (secondLink.first.supportingSegment graph).start.1
        (secondLink.first.supportingSegment graph).finish.1) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstBounds :=
    retainedDrawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal firstMem firstHorizontal
  have secondBounds :=
    retainedDrawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal secondMem secondHorizontal
  simp only [planarMacroScale] at firstBounds secondBounds
  unfold GridSegment.OpenIntervalsOverlap at disjoint
  have separated :
      max (firstLink.first.supportingSegment graph).start.1
            (firstLink.first.supportingSegment graph).finish.1 ≤
          min (secondLink.first.supportingSegment graph).start.1
            (secondLink.first.supportingSegment graph).finish.1 ∨
        max (secondLink.first.supportingSegment graph).start.1
            (secondLink.first.supportingSegment graph).finish.1 ≤
          min (firstLink.first.supportingSegment graph).start.1
            (firstLink.first.supportingSegment graph).finish.1 := by
    omega
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [firstHorizontal, secondHorizontal, if_true]
  rcases separated with firstBefore | secondBefore
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

/-- Vertical selected links whose source intervals have disjoint open
interiors have strictly separated physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_vertical_support_disjoint
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
    (disjoint :
      ¬GridSegment.OpenIntervalsOverlap
        (firstLink.first.supportingSegment graph).start.2
        (firstLink.first.supportingSegment graph).finish.2
        (secondLink.first.supportingSegment graph).start.2
        (secondLink.first.supportingSegment graph).finish.2) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstBounds :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal firstMem firstVertical
  have secondBounds :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal secondMem secondVertical
  simp only [planarMacroScale] at firstBounds secondBounds
  unfold GridSegment.OpenIntervalsOverlap at disjoint
  have separated :
      max (firstLink.first.supportingSegment graph).start.2
            (firstLink.first.supportingSegment graph).finish.2 ≤
          min (secondLink.first.supportingSegment graph).start.2
            (secondLink.first.supportingSegment graph).finish.2 ∨
        max (secondLink.first.supportingSegment graph).start.2
            (secondLink.first.supportingSegment graph).finish.2 ≤
          min (firstLink.first.supportingSegment graph).start.2
            (firstLink.first.supportingSegment graph).finish.2 := by
    omega
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [firstVertical, secondVertical,
    Bool.false_eq_true, if_false]
  rcases separated with firstBefore | secondBefore
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Horizontal selected links on different source rows have strictly
separated physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_normal_ne
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
    (normalDifferent :
      (firstLink.first.supportingSegment graph).start.2 ≠
        (secondLink.first.supportingSegment graph).start.2) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1
  have secondNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  rw [if_pos firstHorizontal] at firstNormal
  rw [if_pos secondHorizontal] at secondNormal
  simp only [planarMacroScale] at firstNormal secondNormal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [firstHorizontal, if_pos, secondHorizontal]
  rcases lt_or_gt_of_ne normalDifferent with lower | higher
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Vertical selected links on different source columns have strictly
separated physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_vertical_normal_ne
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
    (normalDifferent :
      (firstLink.first.supportingSegment graph).start.1 ≠
        (secondLink.first.supportingSegment graph).start.1) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1
  have secondNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  rw [if_neg firstVertical] at firstNormal
  rw [if_neg secondVertical] at secondNormal
  simp only [planarMacroScale] at firstNormal secondNormal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp [firstVertical, secondVertical]
  rcases lt_or_gt_of_ne normalDifferent with lower | higher
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

end PeriodicOrthocrossing
end LeanTrominoes
