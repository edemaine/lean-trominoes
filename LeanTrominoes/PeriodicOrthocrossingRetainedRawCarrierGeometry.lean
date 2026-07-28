import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBoundingBox

/-!
# Geometry of raw retained carrier lenses

The selected retained carrier family keeps one owner from every periodic
orbit.  Periodic separation also needs translated copies of those links,
which can remain in the raw retained carrier window without remaining the
selected owner.  This file exposes the lens boundary and rectangle
certificates for every raw retained link.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A raw retained link advances east or north according to its carrier
axis. -/
theorem retainedDrawingCompleteCarrierLinkRaw_carrierDirection_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    EqualityLink.carrierDirection
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .east else .north := by
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
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

/-- The first port of a raw retained link points forward along its carrier. -/
theorem retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .east else .north := by
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
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

/-- The second port of a raw retained link points backward along its
carrier. -/
theorem retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .west else .south := by
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
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

/-- The generic lens lower corner of a raw retained link is its explicit
carrier rectangle lower corner. -/
theorem retainedDrawingCompleteCarrierLinkRaw_lensRectangleLower_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    EqualityLink.lensRectangleLower
        (CarrierNode.position graph) link =
      drawingCompleteCarrierLinkRectangleLower graph link := by
  unfold EqualityLink.lensRectangleLower
    drawingCompleteCarrierLinkRectangleLower
  rw [retainedDrawingCompleteCarrierLinkRaw_carrierDirection_eq_axis
    wellFormed degree isLocal linkMem]
  by_cases horizontal : link.first.isHorizontal = true
  · simp [horizontal, AxisDirection.equalityLensRectangleLower]
  · simp [horizontal, AxisDirection.equalityLensRectangleLower]

/-- The generic lens upper corner of a raw retained link is its explicit
carrier rectangle upper corner. -/
theorem retainedDrawingCompleteCarrierLinkRaw_lensRectangleUpper_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    EqualityLink.lensRectangleUpper
        (CarrierNode.position graph) link =
      drawingCompleteCarrierLinkRectangleUpper graph link := by
  have clearance :=
    retainedDrawingCompleteCarrierLinkRaw_hasForwardClearance
      wellFormed degree isLocal linkMem
  unfold EqualityLink.lensRectangleUpper
    drawingCompleteCarrierLinkRectangleUpper
  rw [retainedDrawingCompleteCarrierLinkRaw_carrierDirection_eq_axis
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

/-- Every route of a raw retained carrier lens stays outside its first
carrier boundary. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RoutePointsSatisfy
        ((EqualityLink.firstCarrierPort
          (CarrierNode.position formula.incidenceGraph)
          link).OutsideCarrierBoundaryAt
            (EqualityLink.firstCarrierMacroOrigin
              (CarrierNode.position formula.incidenceGraph)
              link)) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routePoints_outsideFirstCarrierBoundary
      (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal linkMem)).rename _ _

/-- Every route of a raw retained carrier lens stays outside its second
carrier boundary. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RoutePointsSatisfy
        ((EqualityLink.secondCarrierPort
          (CarrierNode.position formula.incidenceGraph)
          link).OutsideCarrierBoundaryAt
            (EqualityLink.secondCarrierMacroOrigin
              (CarrierNode.position formula.incidenceGraph)
              link)) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routePoints_outsideSecondCarrierBoundary
      (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal linkMem)).rename _ _

/-- A raw retained carrier lens contacts its first port only at route
endpoints. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RouteContactsAtEndpoint
        (Cell.add
          (EqualityLink.firstCarrierMacroOrigin
            (CarrierNode.position formula.incidenceGraph) link)
          (EqualityLink.firstCarrierPort
            (CarrierNode.position formula.incidenceGraph) link).position) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routeContactsAt_firstCarrierPort
      (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal linkMem)).rename _ _

/-- A raw retained carrier lens contacts its second port only at route
endpoints. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RouteContactsAtEndpoint
        (Cell.add
          (EqualityLink.secondCarrierMacroOrigin
            (CarrierNode.position formula.incidenceGraph) link)
          (EqualityLink.secondCarrierPort
            (CarrierNode.position formula.incidenceGraph) link).position) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routeContactsAt_secondCarrierPort
      (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal linkMem)).rename _ _

/-- Every route point of a raw retained lens lies in its explicit narrow
carrier rectangle. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RoutePointsSatisfy
        (InClosedGridRectangle
          (drawingCompleteCarrierLinkRectangleLower
            formula.incidenceGraph link)
          (drawingCompleteCarrierLinkRectangleUpper
            formula.incidenceGraph link)) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  have bounded :=
    EqualityLink.lensDrawing_routePoints_bounded
      (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal linkMem)
  rw [retainedDrawingCompleteCarrierLinkRaw_lensRectangleLower_eq
      wellFormed degree isLocal linkMem,
    retainedDrawingCompleteCarrierLinkRaw_lensRectangleUpper_eq
      wellFormed degree isLocal linkMem] at bounded
  exact bounded.rename _ _

/-- Separated explicit rectangles separate every genuine route pair of two
raw retained carrier lenses. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_rectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph firstLink)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph firstLink)
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph secondLink)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph secondLink))
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
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded_of_raw
        wellFormed degree isLocal firstMem).of_members
          firstClauseMember firstLiteralMember pointMember
  · intro point pointMember
    exact
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded_of_raw
        wellFormed degree isLocal secondMem).of_members
          secondClauseMember secondLiteralMember pointMember
  · exact rectanglesSeparated

end PeriodicOrthocrossing
end LeanTrominoes
