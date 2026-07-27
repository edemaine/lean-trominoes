import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellCenters

/-!
# Canonical centers of constructed route bends

Every listed point of a constructed route has a unique representative in
the half-open fundamental square.  For inner route points, that
representative has one of eight semantic forms: a fanout midpoint, a port,
a low or high private track at a port, gate, or period boundary.  These
forms provide the finite classification needed to prove that route-bend
macrocells have unique centers.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Representatives in the half-open fundamental square have unique
periodic translates. -/
theorem translatedHalfOpenPositions_eq
    (drawing : PeriodicGridDrawing)
    {first second firstTranslate secondTranslate : Cell}
    (firstBounds :
      0 ≤ first.1 ∧ first.1 < drawing.gridSize ∧
        0 ≤ first.2 ∧ first.2 < drawing.gridSize)
    (secondBounds :
      0 ≤ second.1 ∧ second.1 < drawing.gridSize ∧
        0 ≤ second.2 ∧ second.2 < drawing.gridSize)
    (equal :
      Cell.add first (drawing.periodTranslation firstTranslate) =
        Cell.add second (drawing.periodTranslation secondTranslate)) :
    first = second ∧ firstTranslate = secondTranslate := by
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have horizontal :=
    PeriodicOrthocrossing.periodic_coordinate_unique
      periodPositive
      ⟨firstBounds.1, firstBounds.2.1⟩
      ⟨secondBounds.1, secondBounds.2.1⟩
      (congrArg Prod.fst equal)
  have vertical :=
    PeriodicOrthocrossing.periodic_coordinate_unique
      periodPositive
      ⟨firstBounds.2.2.1, firstBounds.2.2.2⟩
      ⟨secondBounds.2.2.1, secondBounds.2.2.2⟩
      (congrArg Prod.snd equal)
  exact
    ⟨Prod.ext horizontal.1 vertical.1,
      Prod.ext horizontal.2 vertical.2⟩

end PeriodicGridDrawing

namespace PeriodicOrthocrossing

/-- The eight possible semantic forms of an inner constructed-route point
after reducing it to the half-open fundamental square. -/
inductive RouteBendCenterKind (Vertex : Type*)
  | fanout (port : GraphPort Vertex)
  | port (port : GraphPort Vertex)
  | lowPort (port : GraphPort Vertex)
  | highPort (port : GraphPort Vertex)
  | lowGate (edgeIndex : Nat)
  | highGate (edgeIndex : Nat)
  | lowBoundary (edgeIndex : Nat)
  | highBoundary (edgeIndex : Nat)
  deriving DecidableEq, Repr

namespace RouteBendCenterKind

/-- The canonical point in the half-open fundamental square represented by
one semantic bend-center kind. -/
def position
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    RouteBendCenterKind Vertex → Cell
  | .fanout graphPort => (portX graph graphPort, 2)
  | .port graphPort => (portX graph graphPort, 3)
  | .lowPort graphPort =>
      (portX graph graphPort, edgeTrack graphPort.edgeIndex)
  | .highPort graphPort =>
      (portX graph graphPort, edgeTrack graphPort.edgeIndex + 1)
  | .lowGate edgeIndex =>
      (edgeGateX graph edgeIndex, edgeTrack edgeIndex)
  | .highGate edgeIndex =>
      (edgeGateX graph edgeIndex, edgeTrack edgeIndex + 1)
  | .lowBoundary edgeIndex => (0, edgeTrack edgeIndex)
  | .highBoundary edgeIndex => (0, edgeTrack edgeIndex + 1)

/-- A semantic center kind names a genuine port or protoedge index. -/
def Valid
    {Vertex : Type*}
    (graph : PeriodicGraph Vertex) :
    RouteBendCenterKind Vertex → Prop
  | .fanout graphPort
  | .port graphPort
  | .lowPort graphPort
  | .highPort graphPort =>
      graphPort ∈ allPorts graph
  | .lowGate edgeIndex
  | .highGate edgeIndex
  | .lowBoundary edgeIndex
  | .highBoundary edgeIndex =>
      edgeIndex < graph.edges.length

/-- Every genuine port retains an in-range protoedge index. -/
theorem port_edgeIndex_lt_of_mem_allPorts
    {Vertex : Type*}
    (graph : PeriodicGraph Vertex)
    {port : GraphPort Vertex}
    (portMem : port ∈ allPorts graph) :
    port.edgeIndex < graph.edges.length := by
  rcases List.mem_flatMap.mp portMem with
    ⟨taggedEdge, taggedEdgeMem, portMem⟩
  have edgeIndexLt :=
    List.snd_lt_of_mem_zipIdx taggedEdgeMem
  simp [edgePorts] at portMem
  rcases portMem with portEqual | portEqual
  · subst port
    exact edgeIndexLt
  · subst port
    exact edgeIndexLt

/-- Every valid semantic bend center lies in the half-open fundamental
square. -/
theorem position_in_fundamental
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {kind : RouteBendCenterKind Vertex}
    (valid : kind.Valid graph) :
    0 ≤ (kind.position graph).1 ∧
      (kind.position graph).1 < drawingGridSize graph ∧
      0 ≤ (kind.position graph).2 ∧
      (kind.position graph).2 < drawingGridSize graph := by
  cases kind with
  | fanout port | port port | lowPort port | highPort port =>
      change port ∈ allPorts graph at valid
      have portBounds :=
        portX_bounds wellFormed degree valid
      have edgeIndexLt :
          port.edgeIndex < graph.edges.length := by
        exact port_edgeIndex_lt_of_mem_allPorts graph valid
      let taggedEdge :=
        (graph.edges[port.edgeIndex], port.edgeIndex)
      have edgeMem :
          taggedEdge ∈ graph.edges.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨edgeIndexLt, rfl⟩
      have trackBounds := edgeTrack_bounds graph edgeMem
      dsimp [taggedEdge] at trackBounds
      simp only [position]
      constructor
      · omega
      · constructor
        · omega
        · constructor <;> omega
  | lowGate edgeIndex | highGate edgeIndex =>
      change edgeIndex < graph.edges.length at valid
      let taggedEdge :=
        (graph.edges[edgeIndex]'valid, edgeIndex)
      have edgeMem :
          taggedEdge ∈ graph.edges.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨valid, rfl⟩
      have gateBounds := edgeGateX_bounds graph edgeMem
      have trackBounds := edgeTrack_bounds graph edgeMem
      dsimp [taggedEdge] at gateBounds trackBounds
      simp only [position]
      constructor
      · omega
      · constructor
        · omega
        · constructor <;> omega
  | lowBoundary edgeIndex | highBoundary edgeIndex =>
      change edgeIndex < graph.edges.length at valid
      let taggedEdge :=
        (graph.edges[edgeIndex]'valid, edgeIndex)
      have edgeMem :
          taggedEdge ∈ graph.edges.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨valid, rfl⟩
      have trackBounds := edgeTrack_bounds graph edgeMem
      dsimp [taggedEdge] at trackBounds
      simp only [position]
      constructor
      · omega
      · constructor
        · exact_mod_cast drawingGridSize_pos graph
        · constructor <;> omega

/-- The canonical point of a valid semantic bend-center kind determines
that kind uniquely. -/
theorem eq_of_position_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {first second : RouteBendCenterKind Vertex}
    (firstValid : first.Valid graph)
    (secondValid : second.Valid graph)
    (equal : first.position graph = second.position graph) :
    first = second := by
  cases first <;> cases second <;>
    simp only [Valid, position, Prod.mk.injEq,
      edgeTrack, edgeGateX] at firstValid secondValid equal
  all_goals try omega
  case fanout.fanout | port.port |
      lowPort.lowPort | highPort.highPort =>
    congr 1
    exact
      portX_injective_on_allPorts
        wellFormed degree firstValid secondValid equal.1
  case lowGate.lowGate | highGate.highGate |
      lowBoundary.lowBoundary | highBoundary.highBoundary =>
    congr 1
    omega
  case lowPort.lowGate port edgeIndex |
      highPort.highGate port edgeIndex =>
    have separated :=
      portX_lt_edgeGateX
        wellFormed degree firstValid edgeIndex
    simp only [edgeGateX] at separated
    omega
  case lowGate.lowPort edgeIndex port |
      highGate.highPort edgeIndex port =>
    have separated :=
      portX_lt_edgeGateX
        wellFormed degree secondValid edgeIndex
    simp only [edgeGateX] at separated
    omega
  case lowPort.lowBoundary port edgeIndex |
      highPort.highBoundary port edgeIndex =>
    have bounds :=
      portX_bounds wellFormed degree firstValid
    omega
  case lowBoundary.lowPort edgeIndex port |
      highBoundary.highPort edgeIndex port =>
    have bounds :=
      portX_bounds wellFormed degree secondValid
    omega

/-- The protoedge index named by a semantic bend-center kind. -/
def edgeIndex {Vertex : Type*} :
    RouteBendCenterKind Vertex → Nat
  | .fanout graphPort
  | .port graphPort
  | .lowPort graphPort
  | .highPort graphPort =>
      graphPort.edgeIndex
  | .lowGate edgeIndex
  | .highGate edgeIndex
  | .lowBoundary edgeIndex
  | .highBoundary edgeIndex =>
      edgeIndex

end RouteBendCenterKind

/-- A normalized inner route point together with the cell offset needed to
recover its position in the stored (possibly boundary-crossing) route. -/
structure RouteBendCenterPlacement (Vertex : Type*) where
  kind : RouteBendCenterKind Vertex
  offset : Cell
  deriving DecidableEq, Repr

/-- Semantic inner-point placements of one complete constructed route, in
the same order as `routeBends` enumerates them. -/
def routeBendCenterPlacements
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat) :
    List (RouteBendCenterPlacement Vertex) :=
  let source := sourcePort edge edgeIndex
  let target := targetPort edge edgeIndex
  let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
  let targetCenter := vertexX (graph.vertices.idxOf edge.target)
  let sourceColumn := portX graph source
  let targetColumn := portX graph target
  let sourcePlacements :=
    (if sourceCenter = sourceColumn then []
      else [⟨.fanout source, (0, 0)⟩]) ++
      [⟨.port source, (0, 0)⟩]
  let targetPlacements :=
    [⟨.port target, edge.offset⟩] ++
      (if targetCenter = targetColumn then []
      else [⟨.fanout target, edge.offset⟩])
  let trackPlacements :=
    match edge.offset with
    | (0, 0) =>
        [⟨.lowPort source, (0, 0)⟩,
          ⟨.lowPort target, (0, 0)⟩]
    | (1, 0) =>
        if targetColumn < sourceColumn then
          [⟨.lowPort source, (0, 0)⟩,
            ⟨.lowPort target, (1, 0)⟩]
        else
          [⟨.lowPort source, (0, 0)⟩,
            ⟨.lowBoundary edgeIndex, (1, 0)⟩,
            ⟨.highBoundary edgeIndex, (1, 0)⟩,
            ⟨.highPort target, (1, 0)⟩]
    | (-1, 0) =>
        if sourceColumn < targetColumn then
          [⟨.lowPort source, (0, 0)⟩,
            ⟨.lowPort target, (-1, 0)⟩]
        else
          [⟨.lowPort source, (0, 0)⟩,
            ⟨.lowBoundary edgeIndex, (0, 0)⟩,
            ⟨.highBoundary edgeIndex, (0, 0)⟩,
            ⟨.highPort target, (-1, 0)⟩]
    | (0, 1) =>
        [⟨.highPort source, (0, 0)⟩,
          ⟨.highGate edgeIndex, (0, 0)⟩,
          ⟨.lowGate edgeIndex, (0, 1)⟩,
          ⟨.lowPort target, (0, 1)⟩]
    | (0, -1) =>
        [⟨.lowPort source, (0, 0)⟩,
          ⟨.lowGate edgeIndex, (0, 0)⟩,
          ⟨.highGate edgeIndex, (0, -1)⟩,
          ⟨.highPort target, (0, -1)⟩]
    | _ =>
        [⟨.lowPort source, (0, 0)⟩,
          ⟨.lowPort target, edge.offset⟩]
  sourcePlacements ++ trackPlacements ++ targetPlacements

/-- Every semantic placement of a genuine protoedge route names a valid
port or protoedge index. -/
theorem routeBendCenterPlacements_kind_valid
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {placement : RouteBendCenterPlacement Vertex}
    (placementMem :
      placement ∈
        routeBendCenterPlacements graph edge edgeIndex) :
    placement.kind.Valid graph := by
  have sourceMem := sourcePort_mem_allPorts graph edgeMem
  have targetMem := targetPort_mem_allPorts graph edgeMem
  have edgeIndexLt :=
    List.snd_lt_of_mem_zipIdx edgeMem
  simp [routeBendCenterPlacements] at placementMem
  all_goals aesop

/-- One constructed route uses each semantic inner-point kind at most once. -/
theorem routeBendCenterPlacements_kinds_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat) :
    ((routeBendCenterPlacements graph edge edgeIndex).map
      RouteBendCenterPlacement.kind).Nodup := by
  simp only [routeBendCenterPlacements]
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all [sourcePort, targetPort]

/-- Every semantic kind in one route's placement list carries that route's
protoedge index. -/
theorem routeBendCenterPlacements_kind_edgeIndex
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {placement : RouteBendCenterPlacement Vertex}
    (placementMem :
      placement ∈
        routeBendCenterPlacements graph edge edgeIndex) :
    placement.kind.edgeIndex = edgeIndex := by
  simp [routeBendCenterPlacements] at placementMem
  all_goals aesop

set_option maxHeartbeats 500000 in
/-- Within one route, equality of semantic kinds identifies the complete
indexed placements. -/
theorem routeBendCenterPlacements_tagged_eq_of_kind_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {first second : RouteBendCenterPlacement Vertex × Nat}
    (firstMem :
      first ∈
        (routeBendCenterPlacements graph edge edgeIndex).zipIdx)
    (secondMem :
      second ∈
        (routeBendCenterPlacements graph edge edgeIndex).zipIdx)
    (kindEq : first.1.kind = second.1.kind) :
    first = second := by
  let placements :=
    routeBendCenterPlacements graph edge edgeIndex
  have kindsNodup :
      (placements.map RouteBendCenterPlacement.kind).Nodup := by
    exact routeBendCenterPlacements_kinds_nodup
      graph edge edgeIndex
  have firstMapped :
      (first.1.kind, first.2) ∈
        (placements.map RouteBendCenterPlacement.kind).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨first, firstMem, by
        cases first
        rfl⟩
  have secondMapped :
      (second.1.kind, second.2) ∈
        (placements.map RouteBendCenterPlacement.kind).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨second, secondMem, by
        cases second
        rfl⟩
  let firstIndex :
      Fin (placements.map
        RouteBendCenterPlacement.kind).length :=
    ⟨first.2, List.snd_lt_of_mem_zipIdx firstMapped⟩
  let secondIndex :
      Fin (placements.map
        RouteBendCenterPlacement.kind).length :=
    ⟨second.2, List.snd_lt_of_mem_zipIdx secondMapped⟩
  have firstAt :
      (placements.map
        RouteBendCenterPlacement.kind).get firstIndex =
          first.1.kind := by
    simpa [firstIndex] using
      (List.mem_zipIdx' firstMapped).2.symm
  have secondAt :
      (placements.map
        RouteBendCenterPlacement.kind).get secondIndex =
          second.1.kind := by
    simpa [secondIndex] using
      (List.mem_zipIdx' secondMapped).2.symm
  have indexEq :
      firstIndex = secondIndex := by
    apply kindsNodup.injective_get
    exact firstAt.trans (kindEq.trans secondAt.symm)
  apply tagged_eq_of_mem_zipIdx_of_snd_eq
    firstMem secondMem
  exact congrArg Fin.val indexEq

/-- A bend enumerated from a route is the correspondingly indexed inner
point of that route. -/
theorem routeBendsAux_member_bend_zipIdx
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {routeBend : RouteBend},
      routeBend ∈
          routeBendsAux routeIndex translate startIndex points →
        (routeBend.bend, routeBend.incomingSegmentIndex) ∈
          points.tail.dropLast.zipIdx startIndex := by
  intro points
  induction points with
  | nil =>
      intro startIndex routeBend routeBendMem
      simp [routeBendsAux] at routeBendMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex routeBend routeBendMem
          simp [routeBendsAux] at routeBendMem
      | cons second rest =>
          cases rest with
          | nil =>
              intro startIndex routeBend routeBendMem
              simp [routeBendsAux] at routeBendMem
          | cons third rest =>
              intro startIndex routeBend routeBendMem
              simp only [routeBendsAux, List.mem_cons]
                at routeBendMem
              rcases routeBendMem with routeBendEq | routeBendMem
              · subst routeBend
                simp
              · simp only [List.tail_cons, List.dropLast_cons_cons,
                  List.zipIdx_cons, List.mem_cons]
                exact Or.inr
                  (induction (startIndex + 1) routeBendMem)

set_option maxHeartbeats 500000 in
/-- The inner points of a constructed route are exactly its normalized
semantic bend-center placements. -/
theorem constructedEdgeRoute_innerPoints
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    (edgeLocal : edge.span ≤ 1) :
    (constructedEdgeRoute graph edge edgeIndex).tail.dropLast =
      (routeBendCenterPlacements graph edge edgeIndex).map
        (fun placement =>
          Cell.add
            (placement.kind.position graph)
            ((drawing graph).periodTranslation placement.offset)) := by
  let sourceCenter :=
    vertexX (graph.vertices.idxOf edge.source)
  let sourceColumn :=
    portX graph (sourcePort edge edgeIndex)
  let targetCenter :=
    vertexX (graph.vertices.idxOf edge.target)
  let targetColumn :=
    portX graph (targetPort edge edgeIndex)
  rcases offset_eq_of_span_le_one edge edgeLocal with
    offset | offset | offset | offset | offset
  all_goals
    by_cases sourceSame : sourceCenter = sourceColumn <;>
      by_cases targetSame : targetCenter = targetColumn
  all_goals
    simp only [constructedEdgeRoute,
      routeBendCenterPlacements]
  all_goals
    simp_all only [sourceCenter, sourceColumn,
      targetCenter, targetColumn, sourcePort, targetPort]
  all_goals
    by_cases targetBeforeSource :
      portX graph (targetPort edge edgeIndex) <
        portX graph (sourcePort edge edgeIndex) <;>
      by_cases sourceBeforeTarget :
        portX graph (sourcePort edge edgeIndex) <
          portX graph (targetPort edge edgeIndex)
  all_goals
    simp only [sourcePort, targetPort] at targetBeforeSource sourceBeforeTarget
  all_goals try omega
  all_goals
    simp [
      joinPolylines, fanout, edgeCore, translatePolyline,
      RouteBendCenterKind.position,
      PeriodicGridDrawing.periodTranslation,
      drawing_gridSize, Cell.add, Cell.scale,
      sourcePort, targetPort, offset, sourceSame, targetSame,
      targetBeforeSource, sourceBeforeTarget,
      sub_eq_add_neg, add_comm]

/-- Membership in the actual bend list exposes the matching semantic
placement, its within-route index, and its normalized periodic center. -/
theorem constructedEdgeRoute_bend_centerPlacement
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    (translate : Cell)
    (edgeLocal : edge.span ≤ 1)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈
        routeBends edgeIndex translate
          (constructedEdgeRoute graph edge edgeIndex)) :
    ∃ placement placementIndex,
      (placement, placementIndex) ∈
          (routeBendCenterPlacements
            graph edge edgeIndex).zipIdx ∧
        routeBend.routeIndex = edgeIndex ∧
          routeBend.translate = translate ∧
            routeBend.incomingSegmentIndex = placementIndex ∧
              routeBend.drawingPoint graph =
                Cell.add
                  (placement.kind.position graph)
                  ((drawing graph).periodTranslation
                    (Cell.add translate placement.offset)) := by
  have routeBendData :=
    routeBendsAux_member_data edgeIndex translate
      (constructedEdgeRoute graph edge edgeIndex) 0 routeBendMem
  have bendMem :=
    routeBendsAux_member_bend_zipIdx edgeIndex translate
      (constructedEdgeRoute graph edge edgeIndex) 0 routeBendMem
  rw [constructedEdgeRoute_innerPoints graph edge edgeIndex edgeLocal,
    List.zipIdx_map] at bendMem
  rcases List.mem_map.mp bendMem with
    ⟨⟨placement, placementIndex⟩, placementMem, placementEq⟩
  simp only [Prod.map, id_eq, Prod.mk.injEq] at placementEq
  refine ⟨placement, placementIndex, placementMem,
    routeBendData.1, routeBendData.2.1, placementEq.2.symm, ?_⟩
  simp only [RouteBend.drawingPoint]
  rw [routeBendData.2.1]
  rw [← placementEq.1]
  simp [PeriodicGridDrawing.periodTranslation,
    drawing_gridSize, Cell.add, Cell.scale]
  constructor <;> ring

/-- Every bend in the finite drawing enumeration has a unique-period
semantic placement on the protoedge carrying its route. -/
theorem drawingRouteBend_centerPlacement
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    ∃ edge edgeIndex placement placementIndex,
      (edge, edgeIndex) ∈ graph.edges.zipIdx ∧
        (placement, placementIndex) ∈
          (routeBendCenterPlacements
            graph edge edgeIndex).zipIdx ∧
          routeBend.routeIndex = edgeIndex ∧
            routeBend.incomingSegmentIndex = placementIndex ∧
              routeBend.drawingPoint graph =
                Cell.add
                  (placement.kind.position graph)
                  ((drawing graph).periodTranslation
                    (Cell.add routeBend.translate
                      placement.offset)) := by
  rcases List.mem_flatMap.mp routeBendMem with
    ⟨taggedRoute, taggedRouteMem, translatedBendsMem⟩
  rcases List.mem_flatMap.mp translatedBendsMem with
    ⟨translate, _translateMem, routeBendMem⟩
  have edgeIndexLt :
      taggedRoute.2 < graph.edges.length := by
    have routeIndexLt :=
      List.snd_lt_of_mem_zipIdx taggedRouteMem
    simpa [drawing, constructedEdgeRoutes] using routeIndexLt
  let edge : PeriodicEdge Vertex :=
    graph.edges[taggedRoute.2]'edgeIndexLt
  have edgeMem :
      (edge, taggedRoute.2) ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨edgeIndexLt, rfl⟩
  have constructedRouteMem :=
    constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
      graph edgeMem
  have taggedRouteEq :
      taggedRoute =
        (constructedEdgeRoute graph edge taggedRoute.2,
          taggedRoute.2) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      taggedRouteMem constructedRouteMem rfl
  rw [taggedRouteEq] at routeBendMem
  have edgeLocal : edge.span ≤ 1 :=
    isLocal edge (List.fst_mem_of_mem_zipIdx edgeMem)
  rcases
      constructedEdgeRoute_bend_centerPlacement
        graph edge _ translate edgeLocal routeBendMem with
    ⟨placement, placementIndex, placementMem,
      routeEq, translateEq, indexEq, pointEq⟩
  refine ⟨edge, _, placement, placementIndex,
    edgeMem, placementMem, routeEq, indexEq, ?_⟩
  rw [translateEq]
  exact pointEq

/-- Two enumerated route bends with the same drawing point are the same
bend.  Thus every bend macrocell center in the periodic drawing is unique. -/
theorem drawingRouteBends_eq_of_drawingPoint_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (pointEq :
      first.drawingPoint graph =
        second.drawingPoint graph) :
    first = second := by
  rcases drawingRouteBend_centerPlacement
      graph isLocal firstMem with
    ⟨firstEdge, firstEdgeIndex,
      firstPlacement, firstPlacementIndex,
      firstEdgeMem, firstPlacementMem,
      firstRouteEq, firstIndexEq, firstPointEq⟩
  rcases drawingRouteBend_centerPlacement
      graph isLocal secondMem with
    ⟨secondEdge, secondEdgeIndex,
      secondPlacement, secondPlacementIndex,
      secondEdgeMem, secondPlacementMem,
      secondRouteEq, secondIndexEq, secondPointEq⟩
  have firstPlacementListMem :
      firstPlacement ∈
        routeBendCenterPlacements
          graph firstEdge firstEdgeIndex :=
    List.fst_mem_of_mem_zipIdx firstPlacementMem
  have secondPlacementListMem :
      secondPlacement ∈
        routeBendCenterPlacements
          graph secondEdge secondEdgeIndex :=
    List.fst_mem_of_mem_zipIdx secondPlacementMem
  have firstValid :=
    routeBendCenterPlacements_kind_valid
      firstEdgeMem firstPlacementListMem
  have secondValid :=
    routeBendCenterPlacements_kind_valid
      secondEdgeMem secondPlacementListMem
  have normalizedPointEq :
      Cell.add
          (firstPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add first.translate firstPlacement.offset)) =
        Cell.add
          (secondPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add second.translate secondPlacement.offset)) := by
    rw [← firstPointEq, ← secondPointEq]
    exact pointEq
  have normalizedUnique :=
    PeriodicGridDrawing.translatedHalfOpenPositions_eq
      (drawing graph)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree firstValid)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree secondValid)
      normalizedPointEq
  have kindEq :
      firstPlacement.kind = secondPlacement.kind :=
    RouteBendCenterKind.eq_of_position_eq
      wellFormed degree firstValid secondValid
        normalizedUnique.1
  have firstKindIndex :=
    routeBendCenterPlacements_kind_edgeIndex
      graph firstEdge firstEdgeIndex firstPlacementListMem
  have secondKindIndex :=
    routeBendCenterPlacements_kind_edgeIndex
      graph secondEdge secondEdgeIndex secondPlacementListMem
  have edgeIndexEq :
      firstEdgeIndex = secondEdgeIndex :=
    firstKindIndex.symm.trans
      ((congrArg RouteBendCenterKind.edgeIndex kindEq).trans
        secondKindIndex)
  have taggedEdgeEq :
      (firstEdge, firstEdgeIndex) =
        (secondEdge, secondEdgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstEdgeMem secondEdgeMem edgeIndexEq
  have edgeEq : firstEdge = secondEdge :=
    congrArg Prod.fst taggedEdgeEq
  subst secondEdge
  rw [← edgeIndexEq] at secondPlacementMem
  have taggedPlacementEq :
      (firstPlacement, firstPlacementIndex) =
        (secondPlacement, secondPlacementIndex) :=
    routeBendCenterPlacements_tagged_eq_of_kind_eq
      graph firstEdge firstEdgeIndex
        firstPlacementMem secondPlacementMem kindEq
  have placementEq :
      firstPlacement = secondPlacement :=
    congrArg Prod.fst taggedPlacementEq
  have placementIndexEq :
      firstPlacementIndex = secondPlacementIndex :=
    congrArg Prod.snd taggedPlacementEq
  have translateOffsetEq :
      Cell.add first.translate firstPlacement.offset =
        Cell.add second.translate secondPlacement.offset :=
    normalizedUnique.2
  have translateEq :
      first.translate = second.translate := by
    rw [placementEq] at translateOffsetEq
    apply Prod.ext
    · have horizontal :=
        congrArg Prod.fst translateOffsetEq
      simp only [Cell.add] at horizontal
      omega
    · have vertical :=
        congrArg Prod.snd translateOffsetEq
      simp only [Cell.add] at vertical
      omega
  exact
    drawingRouteBends_eq_of_identity_eq
      graph firstMem secondMem
      (firstRouteEq.trans (edgeIndexEq.trans secondRouteEq.symm))
      translateEq
      (firstIndexEq.trans
        (placementIndexEq.trans secondIndexEq.symm))

end PeriodicOrthocrossing
end LeanTrominoes
