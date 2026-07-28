import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierInterfaces

/-!
# Separation of selected retained perpendicular carriers

If horizontal and vertical selected carrier lenses overlapped, their source
occurrences would determine a retained crossover.  The two horizontal ports
of that crossover then lie between the endpoints of the horizontal link.
Strict retained-chain order forces them to be exactly those endpoints, but
the retained chain deliberately filters out such crossover-internal pairs.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A selected horizontal retained lens is strictly separated from every
selected vertical retained lens. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_vertical
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
      ¬verticalLink.first.isHorizontal = true) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph horizontalLink)
      (drawingCompleteCarrierLinkRectangleUpper graph horizontalLink)
      (drawingCompleteCarrierLinkRectangleLower graph verticalLink)
      (drawingCompleteCarrierLinkRectangleUpper graph verticalLink) := by
  by_contra rectanglesOverlap
  let crossing : CrossingRecord :=
    ⟨horizontalLink.first.indexed,
      horizontalLink.first.translate,
      verticalLink.first.indexed,
      verticalLink.first.translate,
      orientedIntersectionPoint
        (horizontalLink.first.supportingSegment graph)
        (verticalLink.first.supportingSegment graph)⟩
  have crossingMem : crossing ∈ retainedCrossings graph := by
    exact
      retainedDrawingCompleteCarrierLinks_crossing_mem_of_horizontal_vertical_overlap
        wellFormed degree isLocal horizontalMem verticalMem
        horizontalTag verticalTag rectanglesOverlap
  let leftBoundary : CrossingBoundary := ⟨crossing, .left⟩
  let rightBoundary : CrossingBoundary := ⟨crossing, .right⟩
  let leftNode : CarrierNode := .boundary leftBoundary
  let rightNode : CarrierNode := .boundary rightBoundary
  have leftBoundaryMem :
      leftBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨crossing, crossingMem, ?_⟩
    simp [leftBoundary]
  have rightBoundaryMem :
      rightBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨crossing, crossingMem, ?_⟩
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
      (horizontalLink.first.position graph).1 ≤
          (verticalLink.first.position graph).1 + 2 ∧
        (verticalLink.first.position graph).1 - 1 ≤
          (horizontalLink.second.position graph).1 := by
    unfold drawingCompleteCarrierLinkRectangleLower
      drawingCompleteCarrierLinkRectangleUpper
      ClosedGridRectanglesSeparated at rectanglesOverlap
    simp only [horizontalTag, verticalTag, Bool.false_eq_true,
      if_true, if_false, not_or] at rectanglesOverlap
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
    simpa [leftNode, leftBoundary, crossing, carrierNodePairLink,
      CrossingBoundary.carrierKey, CarrierNode.carrierKey] using
        (CarrierNode.carrierKey_eq_indexed_translate pair.1).symm
  have rightKey :
      rightNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    simpa [rightNode, rightBoundary, crossing, carrierNodePairLink,
      CrossingBoundary.carrierKey, CarrierNode.carrierKey] using
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
          1 := by
    simp [leftNode, leftBoundary, crossing,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale,
      planarMacroScale, orientedIntersectionPoint]
  have rightCoordinate :
      rightNode.orderCoordinate graph =
        20 *
            (verticalLink.first.supportingSegment graph).start.1 +
          11 := by
    simp [rightNode, rightBoundary, crossing,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale,
      planarMacroScale, orientedIntersectionPoint]
  have firstUpper :
      pair.1.orderCoordinate graph ≤
        (verticalLink.first.position graph).1 + 2 := by
    simpa [carrierNodePairLink, CarrierNode.orderCoordinate,
      firstHorizontal] using overlapData.1
  have secondLower :
      (verticalLink.first.position graph).1 - 1 ≤
        pair.2.orderCoordinate graph := by
    simpa [carrierNodePairLink, CarrierNode.orderCoordinate,
      secondHorizontal] using overlapData.2
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

/-- Selected retained lenses on perpendicular source axes have strictly
separated rectangles, in either orientation. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_perpendicular
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
    (perpendicular :
      CarrierLinksPerpendicular firstLink secondLink) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  rcases perpendicular with
      ⟨firstHorizontal, secondVertical⟩ |
      ⟨firstVertical, secondHorizontal⟩
  · exact
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_vertical
        wellFormed degree isLocal firstMem secondMem
        firstHorizontal secondVertical
  · exact
      (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_vertical
        wellFormed degree isLocal secondMem firstMem
        secondHorizontal firstVertical).symm

/-- Every genuine route pair from two perpendicular selected retained
carrier lenses avoids one another. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_perpendicular
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (perpendicular :
      CarrierLinksPerpendicular firstLink secondLink)
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
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula firstLink).routes
          firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  apply
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_rectanglesSeparated
      wellFormed degree isLocal firstMem secondMem
  · exact
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_perpendicular
        wellFormed degree isLocal firstMem secondMem perpendicular
  · exact firstClauseMember
  · exact firstLiteralMember
  · exact secondClauseMember
  · exact secondLiteralMember

/-- Every genuine route pair from two distinct selected retained carrier
lenses avoids one another. -/
theorem retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (different : firstLink ≠ secondLink)
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
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula firstLink).routes
          firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  by_cases perpendicular :
      CarrierLinksPerpendicular firstLink secondLink
  · exact
      retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_perpendicular
        wellFormed degree isLocal firstMem secondMem perpendicular
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember
  · exact
      retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_not_perpendicular
        wellFormed degree isLocal firstMem secondMem different perpendicular
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
