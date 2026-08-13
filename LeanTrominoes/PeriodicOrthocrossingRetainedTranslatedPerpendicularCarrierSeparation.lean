/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedTranslatedPerpendicularCarrierCore

/-!
# Separation of translated perpendicular retained carriers

If a translated horizontal selected carrier lens overlapped a selected
vertical lens, the physical crossing and its inverse period translate would
both be retained.  The inverse-translated horizontal ports then lie between
the endpoints of the original selected horizontal link.  Consecutive-chain
order forces those ports to be the link endpoints, contradicting the filter
that removes pairs internal to one crossover.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

/-- A translated selected horizontal retained lens is strictly separated
from every selected vertical retained lens. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_vertical
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
    (shift : Cell) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph horizontalLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph horizontalLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph verticalLink)
      (drawingCompleteCarrierLinkRectangleUpper graph verticalLink) := by
  by_contra rectanglesOverlap
  let translatedHorizontal :=
    carrierLinkPeriodTranslate graph horizontalLink shift
  let crossing : CrossingRecord :=
    ⟨translatedHorizontal.first.indexed,
      translatedHorizontal.first.translate,
      verticalLink.first.indexed,
      verticalLink.first.translate,
      orientedIntersectionPoint
        (translatedHorizontal.first.supportingSegment graph)
        (verticalLink.first.supportingSegment graph)⟩
  have crossingData :=
    retainedCarrier_periodTranslate_crossing_and_back_mem_of_horizontal_vertical_overlap
      wellFormed degree isLocal horizontalMem verticalMem
      horizontalTag verticalTag shift rectanglesOverlap
  have crossingMem : crossing ∈ retainedCrossings graph := by
    simpa [crossing, translatedHorizontal] using crossingData.1
  let backCrossing :=
    crossing.periodTranslate graph (Cell.neg shift)
  have backCrossingMem :
      backCrossing ∈ retainedCrossings graph := by
    simpa [backCrossing, crossing, translatedHorizontal] using
      crossingData.2
  let leftBoundary : CrossingBoundary := ⟨backCrossing, .left⟩
  let rightBoundary : CrossingBoundary := ⟨backCrossing, .right⟩
  let leftNode : CarrierNode := .boundary leftBoundary
  let rightNode : CarrierNode := .boundary rightBoundary
  have leftBoundaryMem :
      leftBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨backCrossing, backCrossingMem, ?_⟩
    simp [leftBoundary]
  have rightBoundaryMem :
      rightBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨backCrossing, backCrossingMem, ?_⟩
    simp [rightBoundary]
  have leftNodeMem :
      leftNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_right _
      (List.mem_map.mpr
        ⟨leftBoundary, leftBoundaryMem, rfl⟩)
  have rightNodeMem :
      rightNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_right _
      (List.mem_map.mpr
        ⟨rightBoundary, rightBoundaryMem, rfl⟩)
  have verticalEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      graph verticalMem
  have verticalNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal verticalEndpoints.1
  rw [if_neg verticalTag] at verticalNormal
  simp only [planarMacroScale] at verticalNormal
  have overlapData :
      ((carrierLinkPeriodTranslate graph horizontalLink shift).first
          |>.position graph).1 ≤
          (verticalLink.first.position graph).1 + 2 ∧
        (verticalLink.first.position graph).1 - 1 ≤
          ((carrierLinkPeriodTranslate graph horizontalLink shift).second
            |>.position graph).1 := by
    unfold drawingCompleteCarrierLinkRectangleLower
      drawingCompleteCarrierLinkRectangleUpper
      ClosedGridRectanglesSeparated at rectanglesOverlap
    simp only [carrierLinkPeriodTranslate_first,
      carrierLinkPeriodTranslate_second,
      CarrierNode.isHorizontal_periodTranslate,
      horizontalTag, verticalTag, Bool.false_eq_true,
      if_true, if_false, not_or] at rectanglesOverlap
    simp only [carrierLinkPeriodTranslate_first,
      carrierLinkPeriodTranslate_second]
    omega
  have horizontalRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph horizontalLink).mp horizontalMem).1
  rcases List.mem_flatMap.mp horizontalRaw with
    ⟨key, _keyMem, horizontalLinkMem⟩
  have common :=
    retainedCompleteCarrierLinks_common_key
      graph key horizontalLinkMem
  have keyEqual :
      key = horizontalLink.first.carrierKey :=
    common.1.symm
  subst key
  rcases List.mem_map.mp horizontalLinkMem with
    ⟨pair, pairMem, horizontalLinkEqual⟩
  subst horizontalLink
  have pairData := List.mem_filter.mp pairMem
  have pairMembers := mem_of_mem_consecutivePairs pairData.1
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph (carrierNodePairLink graph pair).first.carrierKey
      pair.1).mp pairMembers.1
  have leftKey :
      leftNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    simpa [leftNode, leftBoundary, backCrossing, crossing,
      translatedHorizontal, carrierNodePairLink,
      CrossingBoundary.carrierKey, CarrierNode.carrierKey,
      CrossingRecord.periodTranslate,
      CarrierNode.carrierKey_eq_indexed_translate,
      CarrierNode.indexed_periodTranslate,
      CarrierNode.translate_periodTranslate,
      Cell.neg, Cell.sub, Cell.add] using
        (CarrierNode.carrierKey_eq_indexed_translate pair.1).symm
  have rightKey :
      rightNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    simpa [rightNode, rightBoundary, backCrossing, crossing,
      translatedHorizontal, carrierNodePairLink,
      CrossingBoundary.carrierKey, CarrierNode.carrierKey,
      CrossingRecord.periodTranslate,
      CarrierNode.carrierKey_eq_indexed_translate,
      CarrierNode.indexed_periodTranslate,
      CarrierNode.translate_periodTranslate,
      Cell.neg, Cell.sub, Cell.add] using
        (CarrierNode.carrierKey_eq_indexed_translate pair.1).symm
  have leftChainMem :
      leftNode ∈ retainedCompleteCarrierNodes graph
        (carrierNodePairLink graph pair).first.carrierKey :=
    (mem_retainedCompleteCarrierNodes_iff
      graph _ leftNode).mpr ⟨leftNodeMem, leftKey⟩
  have rightChainMem :
      rightNode ∈ retainedCompleteCarrierNodes graph
        (carrierNodePairLink graph pair).first.carrierKey :=
    (mem_retainedCompleteCarrierNodes_iff
      graph _ rightNode).mpr ⟨rightNodeMem, rightKey⟩
  have firstLeftAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal firstData.1 leftNodeMem
      (firstData.2.trans leftKey.symm)
  have firstRightAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal firstData.1 rightNodeMem
      (firstData.2.trans rightKey.symm)
  have firstHorizontal :
      pair.1.isHorizontal = true := by
    simpa [carrierNodePairLink] using horizontalTag
  rw [if_pos firstHorizontal] at firstLeftAxis firstRightAxis
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph _ pair.2).mp pairMembers.2
  have secondHorizontal :=
    (retainedCarrierNode_isHorizontal_iff_of_commonCarrier
      wellFormed degree isLocal firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)).mp firstHorizontal
  have leftCoordinate :
      leftNode.orderCoordinate graph =
        20 *
            (verticalLink.first.supportingSegment graph).start.1 +
          1 +
          (carrierMacroPeriodTranslation graph
            (Cell.neg shift)).1 := by
    simp [leftNode, leftBoundary, backCrossing, crossing,
      translatedHorizontal,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale,
      planarMacroScale, orientedIntersectionPoint,
      CrossingRecord.periodTranslate,
      PeriodicGridDrawing.periodTranslation,
      carrierMacroPeriodTranslation, Cell.neg, Cell.sub]
    ring
  have rightCoordinate :
      rightNode.orderCoordinate graph =
        20 *
            (verticalLink.first.supportingSegment graph).start.1 +
          11 +
          (carrierMacroPeriodTranslation graph
            (Cell.neg shift)).1 := by
    simp [rightNode, rightBoundary, backCrossing, crossing,
      translatedHorizontal,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale,
      planarMacroScale, orientedIntersectionPoint,
      CrossingRecord.periodTranslate,
      PeriodicGridDrawing.periodTranslation,
      carrierMacroPeriodTranslation, Cell.neg, Cell.sub]
    ring
  have offsetsCancel :
      (carrierMacroPeriodTranslation graph shift).1 +
          (carrierMacroPeriodTranslation graph
            (Cell.neg shift)).1 =
        0 := by
    rcases shift with ⟨shiftX, shiftY⟩
    simp [carrierMacroPeriodTranslation, Cell.neg,
      Cell.sub, Cell.scale]
  have firstUpper :
      pair.1.orderCoordinate graph +
          (carrierMacroPeriodTranslation graph shift).1 ≤
        (verticalLink.first.position graph).1 + 2 := by
    simpa [carrierNodePairLink,
      CarrierNode.position_periodTranslate, Cell.add,
      CarrierNode.orderCoordinate, firstHorizontal] using
        overlapData.1
  have secondLower :
      (verticalLink.first.position graph).1 - 1 ≤
        pair.2.orderCoordinate graph +
          (carrierMacroPeriodTranslation graph shift).1 := by
    simpa [carrierNodePairLink,
      CarrierNode.position_periodTranslate, Cell.add,
      CarrierNode.orderCoordinate, secondHorizontal] using
        overlapData.2
  have firstMod :
      pair.1.orderCoordinate graph % 10 = 1 := by
    simpa [CarrierNode.orderCoordinate, firstHorizontal] using
      firstLeftAxis.2.1
  have leftMod :
      leftNode.orderCoordinate graph % 10 = 1 := by
    simpa [leftNode, leftBoundary, CarrierNode.orderCoordinate,
      CarrierNode.isHorizontal] using firstLeftAxis.2.2
  have rightMod :
      rightNode.orderCoordinate graph % 10 = 1 := by
    simpa [rightNode, rightBoundary, CarrierNode.orderCoordinate,
      CarrierNode.isHorizontal] using firstRightAxis.2.2
  have secondRightAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal secondData.1 rightNodeMem
      (secondData.2.trans rightKey.symm)
  rw [if_pos secondHorizontal] at secondRightAxis
  have secondMod :
      pair.2.orderCoordinate graph % 10 = 1 := by
    simpa [CarrierNode.orderCoordinate, secondHorizontal] using
      secondRightAxis.2.1
  have firstLeLeft :
      pair.1.orderCoordinate graph ≤
        leftNode.orderCoordinate graph := by
    omega
  have leftLtSecond :
      leftNode.orderCoordinate graph <
        pair.2.orderCoordinate graph := by
    omega
  have firstLtRight :
      pair.1.orderCoordinate graph <
        rightNode.orderCoordinate graph := by
    omega
  have rightLeSecond :
      rightNode.orderCoordinate graph ≤
        pair.2.orderCoordinate graph := by
    omega
  have leftEqual :=
    eq_first_of_mem_consecutivePairs_of_coordinate_between
      (CarrierNode.orderCoordinate graph)
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal
        (carrierNodePairLink graph pair).first.carrierKey)
      pairData.1 leftChainMem firstLeLeft leftLtSecond
  have rightEqual :=
    eq_second_of_mem_consecutivePairs_of_coordinate_between
      (CarrierNode.orderCoordinate graph)
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal
        (carrierNodePairLink graph pair).first.carrierKey)
      pairData.1 rightChainMem firstLtRight rightLeSecond
  have leftEqual' : leftNode = pair.1 := by
    simpa using leftEqual
  have rightEqual' : rightNode = pair.2 := by
    simpa using rightEqual
  have retained := pairData.2
  rw [← leftEqual', ← rightEqual'] at retained
  simp [leftNode, rightNode, leftBoundary, rightBoundary,
    CarrierNode.sameCrossoverSite] at retained

/-- A translated selected vertical retained lens is strictly separated from
every selected horizontal retained lens. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_horizontal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {verticalLink horizontalLink : EqualityLink CarrierNode}
    (verticalMem :
      verticalLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontalMem :
      horizontalLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (verticalTag :
      ¬verticalLink.first.isHorizontal = true)
    (horizontalTag :
      horizontalLink.first.isHorizontal = true)
    (shift : Cell) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph verticalLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph verticalLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph horizontalLink)
      (drawingCompleteCarrierLinkRectangleUpper graph horizontalLink) := by
  have reversed :=
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_vertical
      wellFormed degree isLocal horizontalMem verticalMem
      horizontalTag verticalTag (Cell.neg shift)
  have reversed' := reversed.symm
  simp only [drawingCompleteCarrierLinkRectangleLower_periodTranslate,
    drawingCompleteCarrierLinkRectangleUpper_periodTranslate] at reversed' ⊢
  unfold ClosedGridRectanglesSeparated at reversed' ⊢
  rcases verticalLowerEq :
      drawingCompleteCarrierLinkRectangleLower
        graph verticalLink with ⟨verticalLowerX, verticalLowerY⟩
  rcases verticalUpperEq :
      drawingCompleteCarrierLinkRectangleUpper
        graph verticalLink with ⟨verticalUpperX, verticalUpperY⟩
  rcases horizontalLowerEq :
      drawingCompleteCarrierLinkRectangleLower
        graph horizontalLink with ⟨horizontalLowerX, horizontalLowerY⟩
  rcases horizontalUpperEq :
      drawingCompleteCarrierLinkRectangleUpper
        graph horizontalLink with ⟨horizontalUpperX, horizontalUpperY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp only [verticalLowerEq, verticalUpperEq,
    horizontalLowerEq, horizontalUpperEq,
    carrierMacroPeriodTranslation, Cell.neg,
    Cell.sub, Cell.add, Cell.scale] at reversed' ⊢
  ring_nf at reversed' ⊢
  omega

/-- Any period translate of one selected retained carrier lens is separated
from a selected lens on the perpendicular source axis. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_perpendicular
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
    (shift : Cell)
    (perpendicular :
      CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate graph firstLink shift)
        secondLink) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  rcases perpendicular with
      ⟨firstHorizontal, secondVertical⟩ |
      ⟨firstVertical, secondHorizontal⟩
  · exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_vertical
        wellFormed degree isLocal firstMem secondMem
        (by simpa using firstHorizontal) secondVertical shift
  · exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_horizontal
        wellFormed degree isLocal firstMem secondMem
        (by simpa using firstVertical) secondHorizontal shift

/-- Every genuine route pair from a translated selected carrier and a
perpendicular selected carrier avoids one another. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_periodTranslate_of_perpendicular
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (shift : Cell)
    (perpendicular :
      CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift)
        secondLink)
    {firstClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx)
    {firstLiteral : PlanarSATVariable Variable × Bool}
    {firstLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    {secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx)
    {secondLiteral : PlanarSATVariable Variable × Bool}
    {secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing formula
        (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift)).routes firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  apply
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_periodTranslate_of_rectanglesSeparated
      wellFormed degree isLocal firstMem secondMem shift
  · exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_perpendicular
        wellFormed degree isLocal firstMem secondMem shift perpendicular
  · exact firstClauseMember
  · exact firstLiteralMember
  · exact secondClauseMember
  · exact secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
