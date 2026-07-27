import LeanTrominoes.PeriodicOrthocrossingBendCornerGeometry
import LeanTrominoes.PeriodicOrthocrossingRouteNoImmediateReversal

/-!
# Certified corner drawings for every orthocrossing route bend

Every enumerated bend inherits axis alignment from its constructed route
and the route-wide no-immediate-reversal certificate.  Consequently the
fixed corner equality drawing applies to every bend link in the aggregate
family, with exact endpoint positions and complete local validity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every bend enumerated from one orthogonal no-reversal route has the
local geometry required by the fixed corner drawing. -/
theorem routeBendsAux_cornerGeometry
    (routeIndex : Nat) (translate : Cell)
    {points : List Cell} {incomingSegmentIndex : Nat}
    (orthogonal : OrthogonalPolyline points)
    (noReversal :
      AxisDirection.HasNoImmediateReversal points)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈
        routeBendsAux routeIndex translate
          incomingSegmentIndex points) :
    routeBend.CornerGeometry := by
  induction points generalizing incomingSegmentIndex with
  | nil =>
      simp [routeBendsAux] at routeBendMem
  | cons incomingStart rest induction =>
      cases rest with
      | nil =>
          simp [routeBendsAux] at routeBendMem
      | cons bend rest =>
          cases rest with
          | nil =>
              simp [routeBendsAux] at routeBendMem
          | cons outgoingFinish rest =>
              have firstParts :=
                (List.isChain_cons_cons.mp orthogonal :
                  (GridSegment.mk incomingStart bend).IsAxisAligned ∧
                    OrthogonalPolyline
                      (bend :: outgoingFinish :: rest))
              have outgoingAligned :=
                (List.isChain_cons_cons.mp firstParts.2).1
              simp only [routeBendsAux, List.mem_cons]
                at routeBendMem
              rcases routeBendMem with routeBendEq | routeBendMem
              · subst routeBend
                exact
                  ⟨firstParts.1, outgoingAligned,
                    noReversal.1⟩
              · exact induction firstParts.2 noReversal.2 routeBendMem

/-- Public wrapper for bends enumerated from one complete route. -/
theorem routeBends_cornerGeometry
    (routeIndex : Nat) (translate : Cell)
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points)
    (noReversal :
      AxisDirection.HasNoImmediateReversal points)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ routeBends routeIndex translate points) :
    routeBend.CornerGeometry := by
  exact routeBendsAux_cornerGeometry
    routeIndex translate orthogonal noReversal routeBendMem

/-- Every bend in the neighboring translated drawing block inherits valid
corner geometry from its underlying local protoedge route. -/
theorem drawingRouteBend_cornerGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    routeBend.CornerGeometry := by
  rcases List.mem_flatMap.mp routeBendMem with
    ⟨taggedRoute, taggedRouteMem, routeBendMem⟩
  rcases List.mem_flatMap.mp routeBendMem with
    ⟨translate, _translateMem, routeBendMem⟩
  have routeMem :
      taggedRoute.1 ∈ (drawing graph).edgeRoutes :=
    List.fst_mem_of_mem_zipIdx taggedRouteMem
  change taggedRoute.1 ∈ constructedEdgeRoutes graph at routeMem
  rw [constructedEdgeRoutes] at routeMem
  rcases List.mem_map.mp routeMem with
    ⟨taggedEdge, edgeMem, routeEq⟩
  have edgeLocal : taggedEdge.1.span ≤ 1 :=
    isLocal taggedEdge.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  apply routeBends_cornerGeometry
    taggedRoute.2 translate (points := taggedRoute.1)
  · rw [← routeEq]
    exact constructedEdgeRoute_orthogonal
      wellFormed degree edgeMem edgeLocal
  · rw [← routeEq]
    exact constructedEdgeRoute_hasNoImmediateReversal
      wellFormed degree edgeMem edgeLocal
  · exact routeBendMem

/-- Deduplication preserves every bend's corner-geometry certificate. -/
theorem drawingRouteBendDedup_cornerGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup) :
    routeBend.CornerGeometry :=
  drawingRouteBend_cornerGeometry
    wellFormed degree isLocal (List.mem_dedup.mp routeBendMem)

/-- Every aggregate bend-corner drawing recovers the exact position of its
incoming carrier endpoint. -/
theorem drawingRouteBend_cornerDrawing_firstPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup) :
    (routeBend.cornerDrawing graph).variablePosition
        (routeBend.equalityLink graph).first =
      CarrierNode.position graph
        (routeBend.equalityLink graph).first :=
  routeBend.cornerDrawing_firstPosition graph
    (drawingRouteBendDedup_cornerGeometry
      wellFormed degree isLocal routeBendMem)

/-- Every aggregate bend-corner drawing recovers the exact position of its
outgoing carrier endpoint. -/
theorem drawingRouteBend_cornerDrawing_secondPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup) :
    (routeBend.cornerDrawing graph).variablePosition
        (routeBend.equalityLink graph).second =
      CarrierNode.position graph
        (routeBend.equalityLink graph).second :=
  routeBend.cornerDrawing_secondPosition graph
    (drawingRouteBendDedup_cornerGeometry
      wellFormed degree isLocal routeBendMem)

/-- Every aggregate bend-corner drawing has exact endpoints, orthogonal
routes, and continuous finite planarity. -/
theorem drawingRouteBend_cornerDrawing_isValid
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup) :
    (routeBend.cornerDrawing graph).IsValid :=
  routeBend.cornerDrawing_isValid graph
    (drawingRouteBendDedup_cornerGeometry
      wellFormed degree isLocal routeBendMem)

/-- Membership in the aggregate bend-link family exposes a certified bend
whose fixed corner drawing realizes that link. -/
theorem drawingRouteBendLink_exists_cornerGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingRouteBendLinks graph) :
    ∃ routeBend,
      routeBend ∈ (drawingRouteBends graph).dedup ∧
        routeBend.equalityLink graph = link ∧
          routeBend.CornerGeometry := by
  rcases List.mem_map.mp linkMem with
    ⟨routeBend, routeBendMem, linkEq⟩
  refine ⟨routeBend, routeBendMem, linkEq, ?_⟩
  exact drawingRouteBendDedup_cornerGeometry
    wellFormed degree isLocal routeBendMem

end PeriodicOrthocrossing
end LeanTrominoes
