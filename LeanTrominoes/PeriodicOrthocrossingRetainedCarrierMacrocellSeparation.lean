import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBoundingBox
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierSupportGeometry
import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellBounds

/-!
# Selected retained carriers versus macrocell components

Every non-carrier planar-SAT component lies in the standard `13 × 13`
route rectangle of one `20 × 20` macrocell.  This file packages the generic
bounding-box separation from a selected carrier lens and extracts the exact
drawing-grid proximity forced when those two rectangles are not separated.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A selected retained carrier route avoids any genuine route contained in
a strictly separated standard macrocell. -/
theorem
    retainedDrawingPlanarSATCarrierRoute_avoids_macrocell_of_rectanglesSeparated
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
        (PeriodicCNF.incidenceGraph formula))
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {otherDrawing :
      EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable)}
    {center : Cell}
    (otherBounded :
      otherDrawing.RoutePointsSatisfy
        (InPlanarSATMacrocell center))
    {otherClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {otherClauseIndex : Nat}
    (otherClauseMember :
      (otherClause, otherClauseIndex) ∈
        otherDrawing.formula.zipIdx)
    {otherLiteral : PlanarSATVariable Variable × Bool}
    {otherLiteralIndex : Nat}
    (otherLiteralMember :
      (otherLiteral, otherLiteralIndex) ∈
        otherClause.literals.zipIdx)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) link)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) link)
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center)) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).routes
          carrierClauseIndex carrierLiteralIndex)
      (otherDrawing.routes
        otherClauseIndex otherLiteralIndex) := by
  apply
    EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
  · intro point pointMember
    exact
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal linkMem).of_members
          carrierClauseMember carrierLiteralMember pointMember
  · intro point pointMember
    exact otherBounded.of_members
      otherClauseMember otherLiteralMember pointMember
  · exact rectanglesSeparated

/-- If a horizontal selected retained lens is not separated from a standard
macrocell, that macrocell lies on its source row and overlaps its axial
interval. -/
theorem
    retainedDrawingCompleteCarrierLink_horizontal_macrocell_overlap_data
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontal : link.first.isHorizontal = true)
    (center : Cell)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center)) :
    (link.first.supportingSegment graph).start.2 = center.2 ∧
      (link.first.position graph).1 ≤
        planarMacroScale * center.1 + 13 ∧
      planarMacroScale * center.1 ≤
        (link.second.position graph).1 := by
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have normal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal endpoints.1
  rw [if_pos horizontal] at normal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    planarSATMacrocellRouteLower
    planarSATMacrocellRouteUpper
    ClosedGridRectanglesSeparated at notSeparated
  simp only [horizontal, if_true, not_or,
    Cell.add, Cell.scale] at notSeparated
  simp only [planarMacroScale] at normal notSeparated ⊢
  omega

/-- If a vertical selected retained lens is not separated from a standard
macrocell, that macrocell lies on its source column and overlaps its axial
interval. -/
theorem
    retainedDrawingCompleteCarrierLink_vertical_macrocell_overlap_data
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (vertical : ¬link.first.isHorizontal = true)
    (center : Cell)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center)) :
    (link.first.supportingSegment graph).start.1 = center.1 ∧
      (link.first.position graph).2 ≤
        planarMacroScale * center.2 + 13 ∧
      planarMacroScale * center.2 ≤
        (link.second.position graph).2 := by
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have normal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal endpoints.1
  rw [if_neg vertical] at normal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    planarSATMacrocellRouteLower
    planarSATMacrocellRouteUpper
    ClosedGridRectanglesSeparated at notSeparated
  simp only [vertical, Bool.false_eq_true, if_false, not_or,
    Cell.add, Cell.scale] at notSeparated
  simp only [planarMacroScale] at normal notSeparated ⊢
  omega

end PeriodicOrthocrossing
end LeanTrominoes
