/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundingBox

/-!
# Bounding boxes of selected retained carrier lenses

Forward clearance fixes every selected retained link's direction and compass
ports from its carrier axis.  The generic equality-lens rectangle therefore
reduces to the existing explicit narrow carrier rectangle, and separated
rectangles separate all genuine route pairs.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A selected retained link advances east or north according to its carrier
axis. -/
theorem retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    EqualityLink.carrierDirection
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .east else .north := by
  have clearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xLt :
        (link.first.position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yLt :
        (link.first.position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        (link.first.position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe]

/-- The first port of a selected retained link points forward along its
carrier. -/
theorem retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .east else .north := by
  have clearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xLt :
        (link.first.position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.firstCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt,
      AxisDirection.firstCarrierPort]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yLt :
        (link.first.position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        (link.first.position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.firstCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe,
      AxisDirection.firstCarrierPort]

/-- The second port of a selected retained link points backward along its
carrier. -/
theorem retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .west else .south := by
  have clearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xLt :
        (link.first.position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.secondCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt,
      AxisDirection.secondCarrierPort]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yLt :
        (link.first.position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        (link.first.position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.secondCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe,
      AxisDirection.secondCarrierPort]

/-- The generic lens lower corner of a selected retained link is its explicit
axis-aligned carrier rectangle lower corner. -/
theorem retainedDrawingCompleteCarrierLink_lensRectangleLower_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    EqualityLink.lensRectangleLower
        (CarrierNode.position graph) link =
      drawingCompleteCarrierLinkRectangleLower graph link := by
  unfold EqualityLink.lensRectangleLower
    drawingCompleteCarrierLinkRectangleLower
  rw [retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
    wellFormed degree isLocal linkMem]
  by_cases horizontal : link.first.isHorizontal = true
  · simp [horizontal,
      AxisDirection.equalityLensRectangleLower]
  · simp [horizontal,
      AxisDirection.equalityLensRectangleLower]

/-- The generic lens upper corner of a selected retained link is its explicit
axis-aligned carrier rectangle upper corner. -/
theorem retainedDrawingCompleteCarrierLink_lensRectangleUpper_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    EqualityLink.lensRectangleUpper
        (CarrierNode.position graph) link =
      drawingCompleteCarrierLinkRectangleUpper graph link := by
  have clearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  unfold EqualityLink.lensRectangleUpper
    drawingCompleteCarrierLinkRectangleUpper
  rw [retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
    wellFormed degree isLocal linkMem]
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xNonnegative :
        0 ≤
          (link.second.position graph).1 -
            (link.first.position graph).1 := by
      omega
    simp [horizontal,
      AxisDirection.equalityLensRectangleUpper,
      EqualityLink.carrierSpan,
      AxisDirection.axisSpan, clearance.1,
      abs_of_nonneg xNonnegative]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yNonnegative :
        0 ≤
          (link.second.position graph).2 -
            (link.first.position graph).2 := by
      omega
    simp [horizontal,
      AxisDirection.equalityLensRectangleUpper,
      EqualityLink.carrierSpan,
      AxisDirection.axisSpan, clearance.1,
      abs_of_nonneg yNonnegative]

/-- Every route point of a selected retained lens lies in its explicit narrow
carrier rectangle. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RoutePointsSatisfy
        (InClosedGridRectangle
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) link)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) link)) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  have bounded :=
    EqualityLink.lensDrawing_routePoints_bounded
      (retainedDrawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMem)
  rw [retainedDrawingCompleteCarrierLink_lensRectangleLower_eq
      wellFormed degree isLocal linkMem,
    retainedDrawingCompleteCarrierLink_lensRectangleUpper_eq
      wellFormed degree isLocal linkMem] at bounded
  exact bounded.rename _ _

/-- Separated explicit rectangles give contact-free separation of every
genuine selected retained carrier route pair. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_rectanglesSeparated
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
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) firstLink)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) firstLink)
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) secondLink)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) secondLink))
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
    EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
  · intro point pointMember
    exact
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal firstMem).of_members
          firstClauseMember firstLiteralMember pointMember
  · intro point pointMember
    exact
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal secondMem).of_members
          secondClauseMember secondLiteralMember pointMember
  · exact rectanglesSeparated

end PeriodicOrthocrossing
end LeanTrominoes
