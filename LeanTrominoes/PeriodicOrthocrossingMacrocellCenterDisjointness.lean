import LeanTrominoes.PeriodicOrthocrossingRouteBendCenters

/-!
# Disjoint planar-SAT macrocell center families

The macrocell construction uses both lifted graph vertices and inner route
points as centers.  This file proves that these two center families are
disjoint.  The key local fact is that a listed fanout midpoint exists only
for a port whose column differs from its incident vertex center.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A semantic fanout placement in a constructed route is genuinely off the
center column of its incident endpoint vertex. -/
theorem routeBendCenterPlacements_fanout_center_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {placement : RouteBendCenterPlacement Vertex}
    (placementMem :
      placement ∈
        routeBendCenterPlacements graph edge edgeIndex)
    {port : GraphPort Vertex}
    (kindEq : placement.kind = .fanout port) :
    vertexX (graph.vertices.idxOf port.vertex) ≠
      portX graph port := by
  simp [routeBendCenterPlacements] at placementMem
  all_goals
    aesop (config := {
      maxRuleApplicationDepth := 50
      warnOnNonterminal := false })
  all_goals simp_all [sourcePort, targetPort]

/-- No semantic placement actually used by a constructed route has the
canonical position of a declared graph vertex. -/
theorem routeBendCenterPlacement_position_ne_vertexPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices)
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {placement : RouteBendCenterPlacement Vertex}
    (placementMem :
      placement ∈
        routeBendCenterPlacements graph edge edgeIndex) :
    placement.kind.position graph ≠
      (drawing graph).vertexPosition graph vertex := by
  intro positionEq
  have valid :=
    routeBendCenterPlacements_kind_valid
      edgeMem placementMem
  cases kind : placement.kind with
  | fanout port =>
      have portMem : port ∈ allPorts graph := by
        simpa [RouteBendCenterKind.Valid, kind] using valid
      have portVertexMem :=
        port_vertex_mem wellFormed portMem
      have rankLt :=
        portRank_lt_three degree portMem
      have horizontalEq :=
        congrArg Prod.fst positionEq
      have vertexIndexEq :
          graph.vertices.idxOf vertex =
            graph.vertices.idxOf port.vertex := by
        simp only [kind, RouteBendCenterKind.position,
          drawing_vertexPosition_of_mem graph vertexMem,
          vertexPosition] at horizontalEq
        unfold portX vertexX at horizontalEq
        omega
      have vertexEq : vertex = port.vertex :=
        (List.idxOf_inj vertexMem).mp vertexIndexEq
      have centerEq :
          vertexX (graph.vertices.idxOf port.vertex) =
            portX graph port := by
        rw [drawing_vertexPosition_of_mem graph vertexMem] at horizontalEq
        simp only [kind, RouteBendCenterKind.position,
          vertexPosition] at horizontalEq
        rw [vertexIndexEq] at horizontalEq
        exact horizontalEq.symm
      exact
        (routeBendCenterPlacements_fanout_center_ne
          graph edge edgeIndex placementMem kind) centerEq
  | port port =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition] at verticalEq
  | lowPort port =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition, edgeTrack] at verticalEq
      omega
  | highPort port =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition, edgeTrack] at verticalEq
      omega
  | lowGate gateIndex =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition, edgeTrack] at verticalEq
      omega
  | highGate gateIndex =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition, edgeTrack] at verticalEq
      omega
  | lowBoundary boundaryIndex =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition, edgeTrack] at verticalEq
      omega
  | highBoundary boundaryIndex =>
      have verticalEq :=
        congrArg Prod.snd positionEq
      rw [kind] at verticalEq
      rw [drawing_vertexPosition_of_mem graph vertexMem] at verticalEq
      simp [RouteBendCenterKind.position, vertexPosition, edgeTrack] at verticalEq
      omega

/-- A route-bend center in the infinite periodic lift cannot be a lifted
declared graph-vertex position. -/
theorem drawingRouteBend_drawingPoint_ne_liftedVertexPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices)
    (vertexTranslate : Cell)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    routeBend.drawingPoint graph ≠
      Cell.add
        ((drawing graph).vertexPosition graph vertex)
        ((drawing graph).periodTranslation vertexTranslate) := by
  intro centersEqual
  rcases drawingRouteBend_centerPlacement
      graph isLocal routeBendMem with
    ⟨edge, edgeIndex, placement, placementIndex,
      edgeMem, placementMem, _routeEq, _indexEq,
      bendPointEq⟩
  have placementListMem :
      placement ∈
        routeBendCenterPlacements graph edge edgeIndex :=
    List.fst_mem_of_mem_zipIdx placementMem
  have placementValid :=
    routeBendCenterPlacements_kind_valid
      edgeMem placementListMem
  have normalizedEqual :
      Cell.add
          (placement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add routeBend.translate placement.offset)) =
        Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation vertexTranslate) := by
    rw [← bendPointEq]
    exact centersEqual
  have vertexBoundsOpen :=
    drawing_vertexPosition_in_fundamental_square
      graph vertexMem
  have vertexBounds :
      0 ≤ ((drawing graph).vertexPosition graph vertex).1 ∧
        ((drawing graph).vertexPosition graph vertex).1 <
          (drawing graph).gridSize ∧
        0 ≤ ((drawing graph).vertexPosition graph vertex).2 ∧
        ((drawing graph).vertexPosition graph vertex).2 <
          (drawing graph).gridSize := by
    exact
      ⟨le_of_lt vertexBoundsOpen.1,
        vertexBoundsOpen.2.1,
        le_of_lt vertexBoundsOpen.2.2.1,
        vertexBoundsOpen.2.2.2⟩
  have normalizedUnique :=
    PeriodicGridDrawing.translatedHalfOpenPositions_eq
      (drawing graph)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree placementValid)
      vertexBounds normalizedEqual
  exact
    (routeBendCenterPlacement_position_ne_vertexPosition
      wellFormed degree vertexMem edgeMem placementListMem)
      normalizedUnique.1

end PeriodicOrthocrossing
end LeanTrominoes
