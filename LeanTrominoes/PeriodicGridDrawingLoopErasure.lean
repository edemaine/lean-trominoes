/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes

/-!
# Loop erasure for periodic grid drawings

Pointwise orthogonal loop erasure changes only the stored edge routes of a
periodic drawing.  This module records the drawing-level transport facts used
by the retained hardness construction: exact endpoints and compatibility are
preserved, every normalized route is orthogonal and consists of unit steps,
and convex fundamental-square or halo bounds survive the inserted subdivision
points.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- Normalize every stored route by unit subdivision followed by verified
loop erasure. -/
def normalizeOrthogonalRoutes (drawing : PeriodicGridDrawing) :
    PeriodicGridDrawing where
  gridSizePred := drawing.gridSizePred
  vertexPositions := drawing.vertexPositions
  edgeRoutes :=
    drawing.edgeRoutes.map AxisDirection.normalizeOrthogonalPolyline

@[simp]
theorem normalizeOrthogonalRoutes_gridSize
    (drawing : PeriodicGridDrawing) :
    drawing.normalizeOrthogonalRoutes.gridSize = drawing.gridSize :=
  rfl

@[simp]
theorem normalizeOrthogonalRoutes_periodTranslation
    (drawing : PeriodicGridDrawing) (translate : Cell) :
    drawing.normalizeOrthogonalRoutes.periodTranslation translate =
      drawing.periodTranslation translate :=
  rfl

@[simp]
theorem normalizeOrthogonalRoutes_vertexPosition
    {Vertex : Type*} [BEq Vertex]
    (drawing : PeriodicGridDrawing)
    (graph : PeriodicGraph Vertex) (vertex : Vertex) :
    drawing.normalizeOrthogonalRoutes.vertexPosition graph vertex =
      drawing.vertexPosition graph vertex :=
  rfl

@[simp]
theorem normalizeOrthogonalRoutes_edgeRoute
    (drawing : PeriodicGridDrawing) (edgeIndex : Nat) :
    drawing.normalizeOrthogonalRoutes.edgeRoute edgeIndex =
      AxisDirection.normalizeOrthogonalPolyline
        (drawing.edgeRoute edgeIndex) := by
  unfold normalizeOrthogonalRoutes edgeRoute
  have normalizeNil :
      AxisDirection.normalizeOrthogonalPolyline [] = [] := by
    simp [AxisDirection.normalizeOrthogonalPolyline]
  simpa only [normalizeNil] using
    (List.getD_map
      (l := drawing.edgeRoutes) (d := [])
      (n := edgeIndex)
      AxisDirection.normalizeOrthogonalPolyline)

/-- A route predicate holding pointwise for the source drawing and preserved
by orthogonal normalization holds for the normalized drawing. -/
theorem normalizeOrthogonalRoutes_routewise
    {drawing : PeriodicGridDrawing}
    {predicate : List Cell → Prop}
    (preserved :
      ∀ route ∈ drawing.edgeRoutes,
        predicate (AxisDirection.normalizeOrthogonalPolyline route)) :
    ∀ route ∈ drawing.normalizeOrthogonalRoutes.edgeRoutes,
      predicate route := by
  intro route routeMember
  rcases List.mem_map.mp routeMember with
    ⟨sourceRoute, sourceMember, rfl⟩
  exact preserved sourceRoute sourceMember

/-- Exact route endpoints, together with agreement between the route and
edge counts, imply that every stored route is nonempty. -/
theorem edgeRoutes_nonempty_of_routesMatch
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing}
    (routesMatch : drawing.RoutesMatch graph)
    (routeLength : drawing.edgeRoutes.length = graph.edges.length) :
    ∀ route ∈ drawing.edgeRoutes, route ≠ [] := by
  intro route routeMember routeEmpty
  rcases List.mem_iff_getElem.mp routeMember with
    ⟨routeIndex, routeIndexLt, routeAt⟩
  have edgeIndexLt : routeIndex < graph.edges.length := by
    rwa [← routeLength]
  have taggedEdgeMember :
      (graph.edges[routeIndex], routeIndex) ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨edgeIndexLt, rfl⟩
  have endpoints :=
    routesMatch (graph.edges[routeIndex], routeIndex)
      taggedEdgeMember
  have routeLookup : drawing.edgeRoute routeIndex = route := by
    unfold edgeRoute
    rw [List.getD_eq_getElem _ _ routeIndexLt, routeAt]
  rw [routeLookup, routeEmpty] at endpoints
  simp at endpoints

/-- Normalization preserves exact graph endpoints for an orthogonal drawing
whose advertised routes are nonempty. -/
theorem routesMatch_normalizeOrthogonalRoutes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (routesMatch : drawing.RoutesMatch graph)
    (routeLength : drawing.edgeRoutes.length = graph.edges.length)
    (orthogonal : drawing.IsOrthogonal)
    (routesNonempty :
      ∀ route ∈ drawing.edgeRoutes, route ≠ []) :
    drawing.normalizeOrthogonalRoutes.RoutesMatch graph := by
  intro taggedEdge taggedEdgeMember
  have edgeIndexLt :
      taggedEdge.2 < drawing.edgeRoutes.length := by
    have graphIndexLt : taggedEdge.2 < graph.edges.length :=
      List.snd_lt_of_mem_zipIdx taggedEdgeMember
    rwa [routeLength]
  have routeMember :
      drawing.edgeRoute taggedEdge.2 ∈ drawing.edgeRoutes := by
    unfold edgeRoute
    rw [List.getD_eq_getElem _ _ edgeIndexLt]
    exact List.get_mem drawing.edgeRoutes ⟨taggedEdge.2, edgeIndexLt⟩
  have routeNonempty :=
    routesNonempty (drawing.edgeRoute taggedEdge.2) routeMember
  have routeOrthogonal :=
    (isOrthogonal_iff_routes drawing).mp orthogonal
      _ routeMember
  have endpoints := routesMatch taggedEdge taggedEdgeMember
  rw [normalizeOrthogonalRoutes_edgeRoute]
  constructor
  · rw [AxisDirection.normalizeOrthogonalPolyline_head?
      routeNonempty routeOrthogonal]
    exact endpoints.1
  · rw [AxisDirection.normalizeOrthogonalPolyline_getLast?
      routeNonempty routeOrthogonal]
    exact endpoints.2

/-- Pointwise loop erasure turns all nonempty orthogonal stored routes into
orthogonal routes. -/
theorem isOrthogonal_normalizeOrthogonalRoutes
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal)
    (routesNonempty :
      ∀ route ∈ drawing.edgeRoutes, route ≠ []) :
    drawing.normalizeOrthogonalRoutes.IsOrthogonal := by
  rw [isOrthogonal_iff_routes]
  apply normalizeOrthogonalRoutes_routewise
  intro route routeMember
  exact AxisDirection.normalizeOrthogonalPolyline_orthogonal
    (routesNonempty route routeMember)
    ((isOrthogonal_iff_routes drawing).mp orthogonal
      route routeMember)

/-- Pointwise loop erasure exposes unit lattice steps in every normalized
stored route. -/
theorem hasUnitSteps_normalizeOrthogonalRoutes
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal)
    (routesNonempty :
      ∀ route ∈ drawing.edgeRoutes, route ≠ []) :
    drawing.normalizeOrthogonalRoutes.HasUnitSteps := by
  apply normalizeOrthogonalRoutes_routewise
  intro route routeMember
  exact AxisDirection.normalizeOrthogonalPolyline_unitSteps
    (routesNonempty route routeMember)
    ((isOrthogonal_iff_routes drawing).mp orthogonal
      route routeMember)

/-- Normalization preserves complete drawing compatibility when route
nonemptiness is supplied separately. -/
theorem isCompatible_normalizeOrthogonalRoutes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (orthogonal : drawing.IsOrthogonal)
    (routesNonempty :
      ∀ route ∈ drawing.edgeRoutes, route ≠ []) :
    drawing.normalizeOrthogonalRoutes.IsCompatible graph := by
  rcases compatible with
    ⟨wellFormed, vertexLength, routeLength,
      verticesNodup, vertexBounds, routesMatch⟩
  exact
    ⟨wellFormed, vertexLength,
      by simpa [normalizeOrthogonalRoutes] using routeLength,
      verticesNodup, vertexBounds,
      routesMatch_normalizeOrthogonalRoutes graph drawing
        routesMatch routeLength orthogonal routesNonempty⟩

private theorem normalized_point_provenance
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    {point : Cell}
    (pointMember :
      point ∈ AxisDirection.normalizeOrthogonalPolyline points) :
    point ∈ points ∨
      ∃ segment ∈ gridPolylineSegments points,
        segment.InteriorContains point := by
  have subdividedMember :
      point ∈ AxisDirection.unitSubdividePolyline points :=
    (AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      nonempty orthogonal).subset pointMember
  exact
    AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
      orthogonal subdividedMember

/-- Closed containment in an axis-aligned segment whose endpoints are
strictly inside the fundamental square stays strictly inside that square. -/
private theorem positionInFundamentalSquare_of_contains
    {drawing : PeriodicGridDrawing}
    {segment : GridSegment} {point : Cell}
    (startBounds :
      drawing.PositionInFundamentalSquare segment.start)
    (finishBounds :
      drawing.PositionInFundamentalSquare segment.finish)
    (contains : segment.Contains point) :
    drawing.PositionInFundamentalSquare point := by
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases contains with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · rcases between with between | between <;>
      simp only [GridSegment.IsHorizontal] at horizontal <;>
      simp only [PositionInFundamentalSquare] <;>
      omega
  · rcases between with between | between <;>
      simp only [GridSegment.IsVertical] at vertical <;>
      simp only [PositionInFundamentalSquare] <;>
      omega

/-- Fundamental-square route-point bounds survive normalization. -/
theorem routePointsInFundamentalSquare_normalizeOrthogonalRoutes
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal)
    (routesNonempty :
      ∀ route ∈ drawing.edgeRoutes, route ≠ [])
    (pointsInside : drawing.RoutePointsInFundamentalSquare) :
    drawing.normalizeOrthogonalRoutes.RoutePointsInFundamentalSquare := by
  intro normalizedRoute normalizedMember point pointMember
  rcases List.mem_map.mp normalizedMember with
    ⟨route, routeMember, normalizedEqual⟩
  subst normalizedRoute
  have routeOrthogonal :=
    (isOrthogonal_iff_routes drawing).mp orthogonal route routeMember
  rcases normalized_point_provenance
      (routesNonempty route routeMember) routeOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · change drawing.PositionInFundamentalSquare point
    exact pointsInside route routeMember point originalMember
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    have contained : drawing.PositionInFundamentalSquare point :=
      positionInFundamentalSquare_of_contains
        (drawing := drawing)
        (pointsInside route routeMember segment.start endpoints.1)
        (pointsInside route routeMember segment.finish endpoints.2)
        (GridSegment.contains_of_interiorContains interior)
    change drawing.PositionInFundamentalSquare point
    exact contained

/-- Open one-cell halo route-point bounds survive normalization. -/
theorem routePointsInExpandedSquare_normalizeOrthogonalRoutes
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal)
    (routesNonempty :
      ∀ route ∈ drawing.edgeRoutes, route ≠ [])
    (pointsInside : drawing.RoutePointsInExpandedSquare) :
    drawing.normalizeOrthogonalRoutes.RoutePointsInExpandedSquare := by
  intro normalizedRoute normalizedMember point pointMember
  rcases List.mem_map.mp normalizedMember with
    ⟨route, routeMember, normalizedEqual⟩
  subst normalizedRoute
  have routeOrthogonal :=
    (isOrthogonal_iff_routes drawing).mp orthogonal route routeMember
  rcases normalized_point_provenance
      (routesNonempty route routeMember) routeOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · change drawing.PositionInExpandedSquare point
    exact pointsInside route routeMember point originalMember
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    have contained : drawing.PositionInExpandedSquare point :=
      expanded_of_contains
        (drawing := drawing)
        (pointsInside route routeMember segment.start endpoints.1)
        (pointsInside route routeMember segment.finish endpoints.2)
        (GridSegment.contains_of_interiorContains interior)
    change drawing.PositionInExpandedSquare point
    exact contained

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- Pointwise loop erasure of a positioned incidence-route family. -/
def normalizeOrthogonalIncidenceRoutes
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    AxisDirection.normalizeOrthogonalPolyline
      (routes clauseIndex literalIndex)

/-- Assembling pointwise normalized incidence routes is exactly normalization
of the assembled periodic drawing. -/
theorem incidenceDrawing_normalizeOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) :
    incidenceDrawing source placement
        (normalizeOrthogonalIncidenceRoutes routes) =
      (incidenceDrawing source placement routes).normalizeOrthogonalRoutes := by
  apply PeriodicGridDrawing.equivData.injective
  simp only [PeriodicGridDrawing.equivData, incidenceDrawing,
    PeriodicGridDrawing.normalizeOrthogonalRoutes]
  congr 2
  unfold incidenceEdgeRoutes normalizeOrthogonalIncidenceRoutes
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _
  simp only [List.map_map, Function.comp_def]

/-- An incidence drawing with exact endpoints and orthogonal routes retains
exact endpoints after normalization.  Its route count is supplied by the
incidence-drawing construction itself. -/
theorem routesMatch_incidenceDrawing_normalizeOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph)
    (orthogonal :
      (incidenceDrawing source placement routes).IsOrthogonal) :
    (incidenceDrawing source placement routes).normalizeOrthogonalRoutes.RoutesMatch
      source.erase.incidenceGraph := by
  have routeLength := incidenceEdgeRoutes_length source routes
  exact PeriodicGridDrawing.routesMatch_normalizeOrthogonalRoutes
    source.erase.incidenceGraph
    (incidenceDrawing source placement routes)
    routesMatch routeLength orthogonal
      (PeriodicGridDrawing.edgeRoutes_nonempty_of_routesMatch
        routesMatch routeLength)

/-- An orthogonal incidence drawing with exact endpoints remains orthogonal
after normalization. -/
theorem isOrthogonal_incidenceDrawing_normalizeOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph)
    (orthogonal :
      (incidenceDrawing source placement routes).IsOrthogonal) :
    (incidenceDrawing source placement routes).normalizeOrthogonalRoutes.IsOrthogonal := by
  have routeLength := incidenceEdgeRoutes_length source routes
  exact PeriodicGridDrawing.isOrthogonal_normalizeOrthogonalRoutes
    (incidenceDrawing source placement routes) orthogonal
      (PeriodicGridDrawing.edgeRoutes_nonempty_of_routesMatch
        routesMatch routeLength)

namespace CanonicalOrthogonalIncidenceRoutes

/-- A genuine canonical route is nonempty because its head is an advertised
clause endpoint. -/
theorem route_ne_nil
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family : CanonicalOrthogonalIncidenceRoutes source placement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    family.routes clauseIndex literalIndex ≠ [] := by
  intro routeEmpty
  have endpoints :=
    family.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  simp [routeEmpty] at endpoints

/-- Canonical endpoint and orthogonality certificates survive pointwise loop
erasure. -/
def normalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family : CanonicalOrthogonalIncidenceRoutes source placement) :
    CanonicalOrthogonalIncidenceRoutes source placement where
  routes := normalizeOrthogonalIncidenceRoutes family.routes
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have nonempty :=
      family.route_ne_nil clauseMember literalMember
    have orthogonal :=
      family.orthogonal clause clauseIndex clauseMember
        literal literalIndex literalMember
    have endpoints :=
      family.endpoints clause clauseIndex clauseMember
        literal literalIndex literalMember
    constructor
    · simpa only [normalizeOrthogonalIncidenceRoutes,
        AxisDirection.normalizeOrthogonalPolyline_head?
          nonempty orthogonal] using endpoints.1
    · simpa only [normalizeOrthogonalIncidenceRoutes,
        AxisDirection.normalizeOrthogonalPolyline_getLast?
          nonempty orthogonal] using endpoints.2
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      AxisDirection.normalizeOrthogonalPolyline_orthogonal
        (family.route_ne_nil clauseMember literalMember)
        (family.orthogonal clause clauseIndex clauseMember
          literal literalIndex literalMember)

/-- Every genuine route in a normalized canonical family consists of unit
axis steps. -/
theorem normalize_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family : CanonicalOrthogonalIncidenceRoutes source placement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ((family.normalize).routes clauseIndex literalIndex).IsChain
      AxisDirection.IsUnitAxisStep := by
  exact AxisDirection.normalizeOrthogonalPolyline_unitSteps
    (family.route_ne_nil clauseMember literalMember)
    (family.orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember)

/-- Every genuine route in a normalized canonical family is geometrically
simple. -/
theorem normalize_routeIsSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family : CanonicalOrthogonalIncidenceRoutes source placement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      ((family.normalize).routes clauseIndex literalIndex) := by
  exact AxisDirection.normalizeOrthogonalPolyline_isSimple
    (family.route_ne_nil clauseMember literalMember)
    (family.orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember)

end CanonicalOrthogonalIncidenceRoutes

end PositionedPeriodicCNF
end LeanTrominoes
