/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATEqualityLensBoundingBox
import LeanTrominoes.PeriodicOrthocrossingCarrierAxisInterface
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings

/-!
# Physical bounding boxes of retained carrier lenses

Retained carrier links always advance east or north.  Their generic
equality-lens rectangles therefore simplify to explicit narrow boxes between
the two physical carrier-node positions.  The bounds survive the final
planar-SAT variable renaming.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Explicit lower corner of a retained carrier link's narrow corridor. -/
def drawingCompleteCarrierLinkRectangleLower
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) : Cell :=
  if link.first.isHorizontal then
    ((link.first.position graph).1,
      (link.first.position graph).2 - 2)
  else
    ((link.first.position graph).1 - 1,
      (link.first.position graph).2)

/-- Explicit upper corner of a retained carrier link's narrow corridor. -/
def drawingCompleteCarrierLinkRectangleUpper
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) : Cell :=
  if link.first.isHorizontal then
    ((link.second.position graph).1,
      (link.first.position graph).2 + 1)
  else
    ((link.first.position graph).1 + 2,
      (link.second.position graph).2)

/-- The generic positioned-lens lower corner reduces to the explicit
carrier-axis form. -/
theorem drawingCompleteCarrierLink_lensRectangleLower_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    EqualityLink.lensRectangleLower
        (CarrierNode.position graph) link =
      drawingCompleteCarrierLinkRectangleLower graph link := by
  unfold EqualityLink.lensRectangleLower
    drawingCompleteCarrierLinkRectangleLower
  rw [drawingCompleteCarrierLink_carrierDirection_eq_axis
    wellFormed degree isLocal linkMem]
  by_cases horizontal : link.first.isHorizontal = true
  · simp [horizontal,
      AxisDirection.equalityLensRectangleLower]
  · simp [horizontal,
      AxisDirection.equalityLensRectangleLower]

/-- The generic positioned-lens upper corner reduces to the explicit
carrier-axis form. -/
theorem drawingCompleteCarrierLink_lensRectangleUpper_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    EqualityLink.lensRectangleUpper
        (CarrierNode.position graph) link =
      drawingCompleteCarrierLinkRectangleUpper graph link := by
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  unfold EqualityLink.lensRectangleUpper
    drawingCompleteCarrierLinkRectangleUpper
  rw [drawingCompleteCarrierLink_carrierDirection_eq_axis
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

/-- Every route point of a represented carrier lens lies in the explicit
narrow rectangle between its two carrier nodes. -/
theorem drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
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
      link ∈ drawingCompleteCarrierLinks
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
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMem)
  rw [drawingCompleteCarrierLink_lensRectangleLower_eq
      wellFormed degree isLocal linkMem,
    drawingCompleteCarrierLink_lensRectangleUpper_eq
      wellFormed degree isLocal linkMem] at bounded
  exact bounded.rename _ _

/-- Separation of the explicit carrier rectangles is sufficient for
complete contact-free separation of every selected route pair. -/
theorem
    drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_rectanglesSeparated
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
      firstLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondLink ∈ drawingCompleteCarrierLinks
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
      (drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal firstMem).of_members
          firstClauseMember firstLiteralMember pointMember
  · intro point pointMember
    exact
      (drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal secondMem).of_members
          secondClauseMember secondLiteralMember pointMember
  · exact rectanglesSeparated

end PeriodicOrthocrossing
end LeanTrominoes
