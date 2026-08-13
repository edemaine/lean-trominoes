/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingMacrocellCenterDisjointness
import LeanTrominoes.PeriodicOrthocrossingBendCornerDrawingFamily

/-!
# Crossover centers avoid declared vertices

Canonical crossover records are centered at proper intersections of a
horizontal and a vertical constructed route segment.  This file proves that
such a center cannot be a lifted declared graph vertex.  Track rows are
separated from the vertex row, while a horizontal fanout has a unique
interior grid point one column away from its incident vertex center.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Half-open representatives of one coordinate have unique periodic
translations. -/
theorem translatedHalfOpenCoordinates_eq
    (drawing : PeriodicGridDrawing)
    {first second firstTranslate secondTranslate : Int}
    (firstBounds : 0 ≤ first ∧ first < drawing.gridSize)
    (secondBounds : 0 ≤ second ∧ second < drawing.gridSize)
    (equal :
      first + drawing.gridSize * firstTranslate =
        second + drawing.gridSize * secondTranslate) :
    first = second ∧ firstTranslate = secondTranslate := by
  have zeroBounds :
      0 ≤ (0 : Int) ∧ 0 < drawing.gridSize := by
    constructor
    · exact le_rfl
    · exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have pairEqual :
      Cell.add (first, 0)
          (drawing.periodTranslation (firstTranslate, 0)) =
        Cell.add (second, 0)
          (drawing.periodTranslation (secondTranslate, 0)) := by
    apply Prod.ext
    · simpa [Cell.add, PeriodicGridDrawing.periodTranslation,
        Cell.scale] using equal
    · simp [Cell.add, PeriodicGridDrawing.periodTranslation,
        Cell.scale]
  have unique :=
    drawing.translatedHalfOpenPositions_eq
      ⟨firstBounds.1, firstBounds.2,
        by simp,
        by simpa using zeroBounds.2⟩
      ⟨secondBounds.1, secondBounds.2,
        by simp,
        by simpa using zeroBounds.2⟩
      pairEqual
  exact
    ⟨congrArg Prod.fst unique.1,
      congrArg Prod.fst unique.2⟩

end PeriodicGridDrawing

namespace PeriodicOrthocrossing

/-- A classified horizontal fanout exists only when its port is off the
center column of its incident endpoint vertex. -/
theorem classifiedSegment_horizontalFanout_center_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (fanout : classified.role.IsHorizontalFanout)
    {port : GraphPort Vertex}
    (portEq :
      classified.role.horizontalFanoutPort = some port) :
    vertexX (graph.vertices.idxOf port.vertex) ≠
      portX graph port := by
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  rcases classifiedMem with
    (sourceMem | coreMem) | targetMem
  · simp [classifiedSourceFanout] at sourceMem
    all_goals
      aesop (config := {
        maxRuleApplicationDepth := 50
        warnOnNonterminal := false })
    all_goals
      simp_all [SegmentRole.IsHorizontalFanout,
        SegmentRole.horizontalFanoutPort, sourcePort]
    all_goals subst port
    all_goals contradiction
  · simp [classifiedEdgeCore,
      SegmentRole.IsHorizontalFanout] at coreMem fanout
    all_goals aesop
  · simp [classifiedTargetFanout] at targetMem
    all_goals
      aesop (config := {
        maxRuleApplicationDepth := 50
        warnOnNonterminal := false })
    all_goals
      simp_all [SegmentRole.IsHorizontalFanout,
        SegmentRole.horizontalFanoutPort, targetPort]
    all_goals subst port
    all_goals contradiction

/-- The normalized midpoint of a genuine horizontal fanout is never the
center column of a declared graph vertex. -/
theorem classifiedSegment_horizontalFanout_midpoint_ne_vertexX
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (degree : graph.DegreeAtMost 3)
    {vertex : Vertex}
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (fanout : classified.role.IsHorizontalFanout)
    {port : GraphPort Vertex}
    (portEq :
      classified.role.horizontalFanoutPort = some port)
    (portMem : port ∈ allPorts graph) :
    vertexX (graph.vertices.idxOf vertex) ≠
      fanoutMidpointBase graph classified.role := by
  intro equal
  have rankLt := portRank_lt_three degree portMem
  have offCenter :=
    classifiedSegment_horizontalFanout_center_ne
      graph edge edgeIndex classifiedMem fanout portEq
  cases roleEq : classified.role <;>
    simp_all [SegmentRole.IsHorizontalFanout,
      SegmentRole.horizontalFanoutPort,
      fanoutMidpointBase, portX, vertexX] <;>
    omega

/-- Both endpoints of every translated horizontal fanout have even
horizontal coordinate. -/
theorem horizontalFanout_translated_endpoints_even
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (fanout : classified.role.IsHorizontalFanout)
    (translate : Cell) :
    Even
        ((classified.segment.translate
          ((drawing graph).periodTranslation translate)).start.1) ∧
      Even
        ((classified.segment.translate
          ((drawing graph).periodTranslation translate)).finish.1) := by
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  rcases classifiedMem with
    (sourceMem | coreMem) | targetMem
  · by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at sourceMem
      subst classified
      simp [SegmentRole.IsHorizontalFanout] at fanout
    · simp [classifiedSourceFanout, same] at sourceMem
      rcases sourceMem with classifiedEq | classifiedEq
      · subst classified
        norm_num [GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, drawing_gridSize,
          Cell.add, Cell.scale, drawingGridSize, vertexX, portX,
          parity_simps]
      · subst classified
        simp [SegmentRole.IsHorizontalFanout] at fanout
  · simp [classifiedEdgeCore,
      SegmentRole.IsHorizontalFanout] at coreMem fanout
    all_goals aesop
  · by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at targetMem
      subst classified
      simp [SegmentRole.IsHorizontalFanout] at fanout
    · simp [classifiedTargetFanout, same] at targetMem
      rcases targetMem with classifiedEq | classifiedEq
      · subst classified
        simp [SegmentRole.IsHorizontalFanout] at fanout
      · subst classified
        norm_num [GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, drawing_gridSize,
          Cell.add, Cell.scale, drawingGridSize, vertexX, portX,
          parity_simps]

/-- The unique interior grid point of a translated horizontal fanout has
odd horizontal coordinate. -/
theorem horizontalFanout_interior_point_not_even
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (fanout : classified.role.IsHorizontalFanout)
    (translate point : Cell)
    (contains :
      (classified.segment.translate
        ((drawing graph).periodTranslation translate)).InteriorContains
          point) :
    ¬Even point.1 := by
  rcases horizontalFanout_midpoint_of_interiorContains
      degree edgeMem classifiedMem fanout translate point contains with
    ⟨port, portEq, portMem, pointEq⟩
  have rankLt := portRank_lt_three degree portMem
  have offCenter :=
    classifiedSegment_horizontalFanout_center_ne
      graph edge edgeIndex classifiedMem fanout portEq
  have rankNeOne : portRank graph port ≠ 1 := by
    intro rankEq
    apply offCenter
    simp [portX, rankEq]
  rw [Int.not_even_iff_odd]
  have rankCases :
      portRank graph port = 0 ∨ portRank graph port = 2 := by
    omega
  rcases rankCases with rankEq | rankEq
  · refine
      ⟨4 * (graph.vertices.idxOf port.vertex : Int) + 1 +
          8 * (graph.vertices.length + graph.edges.length + 1) *
            (horizontalFanoutCellShift edge classified.role).1 +
          8 * (graph.vertices.length + graph.edges.length + 1) *
            translate.1, ?_⟩
    rw [pointEq]
    simp [rankEq, drawingGridSize, vertexX]
    ring
  · refine
      ⟨4 * (graph.vertices.idxOf port.vertex : Int) + 2 +
          8 * (graph.vertices.length + graph.edges.length + 1) *
            (horizontalFanoutCellShift edge classified.role).1 +
          8 * (graph.vertices.length + graph.edges.length + 1) *
            translate.1, ?_⟩
    rw [pointEq]
    simp [rankEq, drawingGridSize, vertexX]
    ring

/-! ## Exact classified segments adjacent to an enumerated bend -/

/-- The incoming segment carried by a bend record occurs at the record's
incoming segment index in its source polyline. -/
theorem routeBendsAux_member_incomingSegment_zipIdx
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {routeBend : RouteBend},
      routeBend ∈
          routeBendsAux routeIndex translate startIndex points →
        (⟨routeBend.incomingStart, routeBend.bend⟩,
            routeBend.incomingSegmentIndex) ∈
          (gridPolylineSegments points).zipIdx startIndex := by
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
                simp [gridPolylineSegments]
              · simp only [gridPolylineSegments, List.zipIdx_cons,
                  List.mem_cons]
                exact Or.inr
                  (by
                    simpa only [gridPolylineSegments,
                      List.zipIdx_cons, List.mem_cons,
                      Nat.add_assoc] using
                        induction (startIndex + 1) routeBendMem)

/-- The outgoing segment carried by a bend record occurs immediately after
its incoming segment in its source polyline. -/
theorem routeBendsAux_member_outgoingSegment_zipIdx
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {routeBend : RouteBend},
      routeBend ∈
          routeBendsAux routeIndex translate startIndex points →
        (⟨routeBend.bend, routeBend.outgoingFinish⟩,
            routeBend.incomingSegmentIndex + 1) ∈
          (gridPolylineSegments points).zipIdx startIndex := by
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
                simp [gridPolylineSegments]
              · have tailMem :=
                  induction (startIndex + 1) routeBendMem
                simpa only [gridPolylineSegments,
                  List.zipIdx_cons, List.mem_cons,
                  Nat.add_assoc] using Or.inr tailMem

/-- Every bend in the finite drawing enumeration exposes the two exact
classified segment occurrences adjacent to it. -/
theorem drawingRouteBend_adjacentClassifiedSegments
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    ∃ (edge : PeriodicEdge Vertex) (edgeIndex : Nat)
        (incoming outgoing : ClassifiedSegment Vertex × Nat),
      (edge, edgeIndex) ∈ graph.edges.zipIdx ∧
        incoming ∈
          (classifiedRouteSegments graph edge edgeIndex).zipIdx ∧
        outgoing ∈
          (classifiedRouteSegments graph edge edgeIndex).zipIdx ∧
        routeBend.routeIndex = edgeIndex ∧
        routeBend.incomingSegmentIndex = incoming.2 ∧
        routeBend.incomingSegmentIndex + 1 = outgoing.2 ∧
        incoming.1.segment =
          ⟨routeBend.incomingStart, routeBend.bend⟩ ∧
        outgoing.1.segment =
          ⟨routeBend.bend, routeBend.outgoingFinish⟩ := by
  rcases List.mem_flatMap.mp routeBendMem with
    ⟨taggedRoute, taggedRouteMem, translatedBendsMem⟩
  rcases List.mem_flatMap.mp translatedBendsMem with
    ⟨translate, _translateMem, localBendMem⟩
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
  rw [taggedRouteEq] at localBendMem
  have bendData :=
    routeBendsAux_member_data taggedRoute.2 translate
      (constructedEdgeRoute graph edge taggedRoute.2) 0
      localBendMem
  have incomingMem :=
    routeBendsAux_member_incomingSegment_zipIdx
      taggedRoute.2 translate
      (constructedEdgeRoute graph edge taggedRoute.2) 0
      localBendMem
  have outgoingMem :=
    routeBendsAux_member_outgoingSegment_zipIdx
      taggedRoute.2 translate
      (constructedEdgeRoute graph edge taggedRoute.2) 0
      localBendMem
  rcases exists_classifiedSegment_of_mem incomingMem with
    ⟨incoming, incomingClassifiedMem,
      incomingSegmentEq, incomingIndexEq⟩
  rcases exists_classifiedSegment_of_mem outgoingMem with
    ⟨outgoing, outgoingClassifiedMem,
      outgoingSegmentEq, outgoingIndexEq⟩
  exact
    ⟨edge, taggedRoute.2, incoming, outgoing,
      edgeMem, incomingClassifiedMem, outgoingClassifiedMem,
      bendData.1, incomingIndexEq.symm, outgoingIndexEq.symm,
      incomingSegmentEq, outgoingSegmentEq⟩

/-- Exactly the roles represented by vertical classified segments,
including the unit fanout and boundary pieces that are not active crossing
lanes. -/
def SegmentRole.IsVerticalRole {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourceFanoutVertical _
  | .sourcePortVertical _
  | .gateVertical _
  | .boundaryVertical _
  | .targetPortVertical _
  | .targetFanoutVertical _ => True
  | _ => False

/-- Executable form of `SegmentRole.IsVerticalRole`. -/
def SegmentRole.isVerticalRole {Vertex : Type*} :
    SegmentRole Vertex → Bool
  | .sourceFanoutVertical _
  | .sourcePortVertical _
  | .gateVertical _
  | .boundaryVertical _
  | .targetPortVertical _
  | .targetFanoutVertical _ => true
  | _ => false

theorem SegmentRole.isVerticalRole_eq_true_iff
    {Vertex : Type*} (role : SegmentRole Vertex) :
    role.isVerticalRole = true ↔ role.IsVerticalRole := by
  cases role <;> simp [isVerticalRole, IsVerticalRole]

/-- Whether a semantic route-bend center is the height-three port marker. -/
def RouteBendCenterKind.isPort {Vertex : Type*} :
    RouteBendCenterKind Vertex → Bool
  | .port _ => true
  | _ => false

theorem RouteBendCenterKind.isPort_eq_true_iff
    {Vertex : Type*} (kind : RouteBendCenterKind Vertex) :
    kind.isPort = true ↔ ∃ port, kind = .port port := by
  cases kind <;> simp [isPort]

/-- A geometrically vertical classified segment carries a vertical semantic
role. -/
theorem classifiedSegment_verticalRole_of_isVertical
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (vertical : classified.segment.IsVertical) :
    classified.role.IsVerticalRole := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsVertical → item.role.IsVerticalRole := by
    simp [classifiedSourceFanout, SegmentRole.IsVerticalRole,
      GridSegment.IsVertical]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsVertical → item.role.IsVerticalRole := by
    simp [classifiedEdgeCore, SegmentRole.IsVerticalRole,
      GridSegment.IsVertical, Cell.add, Cell.scale]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsVertical → item.role.IsVerticalRole := by
    simp [classifiedTargetFanout, SegmentRole.IsVerticalRole,
      GridSegment.IsVertical, Cell.add, Cell.scale]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem vertical)
      (fun coreMem =>
        coreAll classified coreMem vertical))
    (fun targetMem =>
      targetAll classified targetMem vertical)

/-- The port flags of the semantic bend placements are exactly the
conjunctions of the vertical flags of consecutive classified segments. -/
theorem routeBendCenterPlacements_map_isPort
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat) :
    (routeBendCenterPlacements graph edge edgeIndex).map
        (fun placement => placement.kind.isPort) =
      let vertical :=
        (classifiedRouteSegments graph edge edgeIndex).map
          (fun classified => classified.role.isVerticalRole)
      List.zipWith (· && ·) vertical vertical.tail := by
  simp [routeBendCenterPlacements,
    classifiedRouteSegments, classifiedSourceFanout,
    classifiedEdgeCore, classifiedTargetFanout,
    SegmentRole.isVerticalRole, RouteBendCenterKind.isPort]
  all_goals split <;> simp_all
  all_goals try split <;> simp_all
  all_goals try split <;> simp_all
  all_goals try split <;> simp_all

/-- In the parallel lists of semantic center placements and classified
roles, two adjacent vertical roles can surround only a port placement. -/
theorem routeBendCenterPlacement_kind_port_of_adjacent_verticalRoles
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {placement : RouteBendCenterPlacement Vertex × Nat}
    (placementMem :
      placement ∈
        (routeBendCenterPlacements
          graph edge edgeIndex).zipIdx)
    {incomingRole outgoingRole : SegmentRole Vertex}
    {incomingIndex outgoingIndex : Nat}
    (incomingRoleMem :
      (incomingRole, incomingIndex) ∈
        ((classifiedRouteSegments graph edge edgeIndex).map
          ClassifiedSegment.role).zipIdx)
    (outgoingRoleMem :
      (outgoingRole, outgoingIndex) ∈
        ((classifiedRouteSegments graph edge edgeIndex).map
          ClassifiedSegment.role).zipIdx)
    (incomingIndexEq : incomingIndex = placement.2)
    (outgoingIndexEq : outgoingIndex = placement.2 + 1)
    (incomingVertical : incomingRole.IsVerticalRole)
    (outgoingVertical : outgoingRole.IsVerticalRole) :
    ∃ port, placement.1.kind = .port port := by
  let roles :=
    (classifiedRouteSegments graph edge edgeIndex).map
      ClassifiedSegment.role
  let vertical :=
    (classifiedRouteSegments graph edge edgeIndex).map
      (fun classified => classified.role.isVerticalRole)
  have placementFlagMem :
      (placement.1.kind.isPort, placement.2) ∈
        ((routeBendCenterPlacements graph edge edgeIndex).map
          (fun item => item.kind.isPort)).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨placement, placementMem, rfl⟩
  have placementFlagAt :=
    (List.mem_zipIdx_iff_getElem?).mp placementFlagMem
  have verticalEq :
      vertical = roles.map SegmentRole.isVerticalRole := by
    simp [vertical, roles, List.map_map]
  have incomingFlagMem :
      (incomingRole.isVerticalRole, incomingIndex) ∈
        vertical.zipIdx := by
    rw [verticalEq, List.zipIdx_map]
    exact
      List.mem_map.mpr
        ⟨(incomingRole, incomingIndex), incomingRoleMem, rfl⟩
  have outgoingFlagMem :
      (outgoingRole.isVerticalRole, outgoingIndex) ∈
        vertical.zipIdx := by
    rw [verticalEq, List.zipIdx_map]
    exact
      List.mem_map.mpr
        ⟨(outgoingRole, outgoingIndex), outgoingRoleMem, rfl⟩
  have incomingFlagAtRaw :=
    (List.mem_zipIdx_iff_getElem?).mp incomingFlagMem
  have outgoingFlagAtRaw :=
    (List.mem_zipIdx_iff_getElem?).mp outgoingFlagMem
  have incomingFlagAt :
      vertical[placement.2]? = some true := by
    rw [← incomingIndexEq, incomingFlagAtRaw]
    simp only [Option.some.injEq]
    exact
      (SegmentRole.isVerticalRole_eq_true_iff incomingRole).mpr
        incomingVertical
  have outgoingFlagAt :
      vertical[placement.2 + 1]? = some true := by
    rw [← outgoingIndexEq, outgoingFlagAtRaw]
    simp only [Option.some.injEq]
    exact
      (SegmentRole.isVerticalRole_eq_true_iff outgoingRole).mpr
        outgoingVertical
  have outgoingTailFlagAt :
      vertical.tail[placement.2]? = some true := by
    simpa only [List.getElem?_tail] using outgoingFlagAt
  have adjacentFlagAt :
      (List.zipWith (· && ·) vertical vertical.tail)[placement.2]? =
        some true := by
    simp [List.getElem?_zipWith, incomingFlagAt, outgoingTailFlagAt]
  rw [routeBendCenterPlacements_map_isPort graph edge edgeIndex]
    at placementFlagAt
  change
    (List.zipWith (· && ·) vertical vertical.tail)[placement.2]? =
      some placement.1.kind.isPort at placementFlagAt
  rw [adjacentFlagAt] at placementFlagAt
  exact
    (RouteBendCenterKind.isPort_eq_true_iff placement.1.kind).mp
      (Option.some.inj placementFlagAt.symm)

set_option maxHeartbeats 500000 in
/-- The only semantic inner point whose adjacent classified segments are
both vertical is the height-three port marker between fanout and core. -/
theorem routeBendCenterPlacement_kind_port_of_adjacent_vertical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {placement : RouteBendCenterPlacement Vertex × Nat}
    (placementMem :
      placement ∈
        (routeBendCenterPlacements
          graph edge edgeIndex).zipIdx)
    {incoming outgoing : ClassifiedSegment Vertex × Nat}
    (incomingMem :
      incoming ∈
        (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (outgoingMem :
      outgoing ∈
        (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (incomingIndex : incoming.2 = placement.2)
    (outgoingIndex : outgoing.2 = placement.2 + 1)
    (incomingVertical : incoming.1.segment.IsVertical)
    (outgoingVertical : outgoing.1.segment.IsVertical) :
    ∃ port, placement.1.kind = .port port := by
  have incomingVerticalRole :=
    classifiedSegment_verticalRole_of_isVertical
      (List.fst_mem_of_mem_zipIdx incomingMem)
      incomingVertical
  have outgoingVerticalRole :=
    classifiedSegment_verticalRole_of_isVertical
      (List.fst_mem_of_mem_zipIdx outgoingMem)
      outgoingVertical
  have incomingRoleMem :
      (incoming.1.role, incoming.2) ∈
        ((classifiedRouteSegments graph edge edgeIndex).map
          ClassifiedSegment.role).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨incoming, incomingMem, rfl⟩
  have outgoingRoleMem :
      (outgoing.1.role, outgoing.2) ∈
        ((classifiedRouteSegments graph edge edgeIndex).map
          ClassifiedSegment.role).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨outgoing, outgoingMem, rfl⟩
  exact
    routeBendCenterPlacement_kind_port_of_adjacent_verticalRoles
      graph edge edgeIndex placementMem
      incomingRoleMem outgoingRoleMem
      incomingIndex outgoingIndex
      incomingVerticalRole outgoingVerticalRole

/-- An endpoint of a horizontal segment whose span is at most one period
cannot lie in the open interior of any periodic translate of that segment. -/
theorem horizontalSegment_translate_not_interiorContains_endpoint
    {segment : GridSegment}
    (horizontal : segment.IsHorizontal)
    {period : Int}
    (periodPositive : 0 < period)
    (spanForward :
      segment.finish.1 - segment.start.1 ≤ period)
    (spanBackward :
      segment.start.1 - segment.finish.1 ≤ period)
    (endpoint : SegmentEnd)
    (segmentTranslate endpointTranslate : Cell) :
    ¬(segment.translate
        (Cell.scale period segmentTranslate)).InteriorContains
      (Cell.add
        (Cell.scale period endpointTranslate)
        (match endpoint with
          | .start => segment.start
          | .finish => segment.finish)) := by
  have endpointNotBetween :
      ∀ endpointX,
        endpointX = segment.start.1 ∨
          endpointX = segment.finish.1 →
        ¬GridSegment.StrictlyBetween
          (period * segmentTranslate.1 + segment.start.1)
          (period * segmentTranslate.1 + segment.finish.1)
          (period * endpointTranslate.1 + endpointX) := by
    intro endpointX endpointEq between
    rcases endpointEq with rfl | rfl
    · by_cases sameShift :
          endpointTranslate.1 = segmentTranslate.1
      · rw [sameShift] at between
        unfold GridSegment.StrictlyBetween at between
        omega
      · rcases lt_or_gt_of_ne sameShift with
          shiftLess | shiftGreater
        · have shiftStep :
              endpointTranslate.1 + 1 ≤
                segmentTranslate.1 := by omega
          have multiplied :=
            mul_le_mul_of_nonneg_left shiftStep
              (le_of_lt periodPositive)
          unfold GridSegment.StrictlyBetween at between
          rcases between with between | between <;>
            nlinarith
        · have shiftStep :
              segmentTranslate.1 + 1 ≤
                endpointTranslate.1 := by omega
          have multiplied :=
            mul_le_mul_of_nonneg_left shiftStep
              (le_of_lt periodPositive)
          unfold GridSegment.StrictlyBetween at between
          rcases between with between | between <;>
            nlinarith
    · by_cases sameShift :
          endpointTranslate.1 = segmentTranslate.1
      · rw [sameShift] at between
        unfold GridSegment.StrictlyBetween at between
        omega
      · rcases lt_or_gt_of_ne sameShift with
          shiftLess | shiftGreater
        · have shiftStep :
              endpointTranslate.1 + 1 ≤
                segmentTranslate.1 := by omega
          have multiplied :=
            mul_le_mul_of_nonneg_left shiftStep
              (le_of_lt periodPositive)
          unfold GridSegment.StrictlyBetween at between
          rcases between with between | between <;>
            nlinarith
        · have shiftStep :
              segmentTranslate.1 + 1 ≤
                endpointTranslate.1 := by omega
          have multiplied :=
            mul_le_mul_of_nonneg_left shiftStep
              (le_of_lt periodPositive)
          unfold GridSegment.StrictlyBetween at between
          rcases between with between | between <;>
            nlinarith
  intro contains
  rcases contains with
    ⟨_translatedHorizontal, sameY, between⟩ |
      ⟨translatedVertical, _sameX, _between⟩
  · cases endpoint with
    | start =>
        apply endpointNotBetween segment.start.1 (Or.inl rfl)
        simpa only [GridSegment.translate, Cell.add,
          Cell.scale] using between
    | finish =>
        apply endpointNotBetween segment.finish.1 (Or.inr rfl)
        simpa only [GridSegment.translate, Cell.add,
          Cell.scale] using between
  · exact
      ((GridSegment.isVertical_translate _ _).mp
        translatedVertical).2 horizontal.1

/-- No periodic copy of the reserved port row at height three contains a
retained crossover center. -/
theorem orientedCrossing_point_snd_ne_portRow
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    (translate : Int) :
    crossing.point.2 ≠
      3 + (drawing graph).gridSize * translate := by
  intro pointYBase
  have sound := orientedCrossingHalo_sound graph crossingMem
  rcases exists_classifiedSegment_of_drawing_mem sound.1 with
    ⟨taggedRoute, taggedRouteMem,
      taggedClassified, taggedClassifiedMem, firstEq⟩
  have edgeMem :
      taggedRoute.1 ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx taggedRouteMem
  have classifiedMem :
      taggedClassified.1 ∈
        classifiedRouteSegments graph
          taggedRoute.1.1 taggedRoute.1.2 :=
    List.fst_mem_of_mem_zipIdx taggedClassifiedMem
  have translatedHorizontal :
      (taggedClassified.1.segment.translate
        ((drawing graph).periodTranslation
          crossing.firstTranslate)).IsHorizontal := by
    simpa [CrossingRecord.firstSegment, firstEq] using
      sound.2.2.2.2.2.1
  have storedHorizontal :
      taggedClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp
      translatedHorizontal
  have horizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      classifiedMem storedHorizontal
  have translatedContains :
      (taggedClassified.1.segment.translate
        ((drawing graph).periodTranslation
          crossing.firstTranslate)).InteriorContains
        crossing.point := by
    simpa [CrossingRecord.firstSegment, firstEq] using
      sound.2.2.2.2.2.2.2.1
  have pointY :
      crossing.point.2 =
        taggedClassified.1.segment.start.2 +
          drawingGridSize graph * crossing.firstTranslate.2 := by
    rcases translatedContains with
      ⟨_horizontal, sameY, _between⟩ |
        ⟨vertical, _sameX, _between⟩
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        drawing_gridSize, Cell.add, Cell.scale,
        add_comm] using sameY
    · exact (translatedHorizontal.2 vertical.1).elim
  have lane :=
    classifiedSegment_horizontal_lane
      classifiedMem horizontalRole
  have laneBounds :=
    horizontalLaneBase_bounds
      edgeMem classifiedMem horizontalRole
  have threeBounds :
      0 ≤ (3 : Int) ∧
        (3 : Int) < (drawing graph).gridSize := by
    rw [drawing_gridSize]
    have sizePositive := drawingGridSize_pos graph
    unfold drawingGridSize at sizePositive ⊢
    omega
  have laneBounds' :
      0 ≤ horizontalLaneBase taggedClassified.1.role ∧
        horizontalLaneBase taggedClassified.1.role <
          (drawing graph).gridSize := by
    simpa [drawing_gridSize] using laneBounds
  have lanePeriodicEqual :
      (3 : Int) + (drawing graph).gridSize * translate =
        horizontalLaneBase taggedClassified.1.role +
          (drawing graph).gridSize *
            (horizontalLaneCellShift taggedRoute.1.1
              taggedClassified.1.role +
                crossing.firstTranslate.2) := by
    rw [drawing_gridSize]
    rw [lane] at pointY
    rw [pointYBase] at pointY
    simpa [mul_add, add_assoc] using pointY
  have laneBaseEqual :=
    ((drawing graph).translatedHalfOpenCoordinates_eq
      threeBounds laneBounds' lanePeriodicEqual).1
  cases roleEq : taggedClassified.1.role <;>
    simp_all [SegmentRole.IsHorizontalRole,
      horizontalLaneBase, edgeTrack] <;>
    omega

/-- The fundamental-copy port row is the zero-translation special case. -/
theorem orientedCrossing_point_snd_ne_three
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph) :
    crossing.point.2 ≠ 3 := by
  simpa using
    orientedCrossing_point_snd_ne_portRow
      (graph := graph) crossingMem 0

/-- A retained proper crossover cannot occur at either endpoint of any
translated horizontal classified route segment. -/
theorem orientedCrossing_point_ne_horizontal_classified_endpoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex × Nat}
    (classifiedMem :
      classified ∈
        (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (horizontal : classified.1.segment.IsHorizontal)
    (translate : Cell)
    (endpoint : SegmentEnd) :
    crossing.point ≠
      Cell.add
        ((drawing graph).periodTranslation translate)
        (match endpoint with
          | .start => classified.1.segment.start
          | .finish => classified.1.segment.finish) := by
  intro pointEq
  have sound := orientedCrossingHalo_sound graph crossingMem
  rcases exists_classifiedSegment_of_drawing_mem sound.1 with
    ⟨crossingRoute, crossingRouteMem,
      crossingClassified, crossingClassifiedMem, firstEq⟩
  have crossingEdgeMem :
      crossingRoute.1 ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx crossingRouteMem
  have crossingClassifiedListMem :
      crossingClassified.1 ∈
        classifiedRouteSegments graph
          crossingRoute.1.1 crossingRoute.1.2 :=
    List.fst_mem_of_mem_zipIdx crossingClassifiedMem
  have crossingTranslatedHorizontal :
      (crossingClassified.1.segment.translate
        ((drawing graph).periodTranslation
          crossing.firstTranslate)).IsHorizontal := by
    simpa [CrossingRecord.firstSegment, firstEq] using
      sound.2.2.2.2.2.1
  have crossingStoredHorizontal :
      crossingClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp
      crossingTranslatedHorizontal
  have crossingHorizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      crossingClassifiedListMem crossingStoredHorizontal
  have endpointHorizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      (List.fst_mem_of_mem_zipIdx classifiedMem) horizontal
  have crossingContains :
      (crossingClassified.1.segment.translate
        ((drawing graph).periodTranslation
          crossing.firstTranslate)).InteriorContains
        crossing.point := by
    simpa [CrossingRecord.firstSegment, firstEq] using
      sound.2.2.2.2.2.2.2.1
  have crossingPointY :
      crossing.point.2 =
        crossingClassified.1.segment.start.2 +
          drawingGridSize graph * crossing.firstTranslate.2 := by
    rcases crossingContains with
      ⟨_horizontal, sameY, _between⟩ |
        ⟨vertical, _sameX, _between⟩
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        drawing_gridSize, Cell.add, Cell.scale,
        add_comm] using sameY
    · exact
        (crossingTranslatedHorizontal.2 vertical.1).elim
  have endpointPointY :
      crossing.point.2 =
        classified.1.segment.start.2 +
          drawingGridSize graph * translate.2 := by
    have coordinateEq := congrArg Prod.snd pointEq
    cases endpoint with
    | start =>
        simpa [PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale,
          add_comm] using coordinateEq
    | finish =>
        calc
          crossing.point.2 =
              drawingGridSize graph * translate.2 +
                classified.1.segment.finish.2 := by
            simpa [PeriodicGridDrawing.periodTranslation,
              drawing_gridSize, Cell.add, Cell.scale] using
                coordinateEq
          _ = drawingGridSize graph * translate.2 +
                classified.1.segment.start.2 := by
            rw [horizontal.1]
          _ = _ := by ring
  have crossingLane :=
    classifiedSegment_horizontal_lane
      crossingClassifiedListMem crossingHorizontalRole
  have endpointLane :=
    classifiedSegment_horizontal_lane
      (List.fst_mem_of_mem_zipIdx classifiedMem)
      endpointHorizontalRole
  have normalizedLanesEqual :
      horizontalLaneBase crossingClassified.1.role +
          drawingGridSize graph *
            (horizontalLaneCellShift
              crossingRoute.1.1 crossingClassified.1.role +
                crossing.firstTranslate.2) =
        horizontalLaneBase classified.1.role +
          drawingGridSize graph *
            (horizontalLaneCellShift edge classified.1.role +
              translate.2) := by
    calc
      _ = crossingClassified.1.segment.start.2 +
          drawingGridSize graph * crossing.firstTranslate.2 := by
            rw [crossingLane]
            ring
      _ = crossing.point.2 := crossingPointY.symm
      _ = classified.1.segment.start.2 +
          drawingGridSize graph * translate.2 := endpointPointY
      _ = _ := by
        rw [endpointLane]
        ring
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have crossingLaneBounds :=
    horizontalLaneBase_bounds
      crossingEdgeMem crossingClassifiedListMem
      crossingHorizontalRole
  have endpointLaneBounds :=
    horizontalLaneBase_bounds
      edgeMem (List.fst_mem_of_mem_zipIdx classifiedMem)
      endpointHorizontalRole
  have normalizedLaneData :=
    periodic_coordinate_unique
      periodPositive crossingLaneBounds endpointLaneBounds
      normalizedLanesEqual
  rcases horizontal_roles_eq_or_both_fanout
      crossingHorizontalRole endpointHorizontalRole
      normalizedLaneData.1 with
    rolesEqual | ⟨crossingFanout, endpointFanout⟩
  · have crossingRoleIndex :=
      classifiedSegment_role_edgeIndex
        crossingClassifiedListMem
    have endpointRoleIndex :=
      classifiedSegment_role_edgeIndex
        (List.fst_mem_of_mem_zipIdx classifiedMem)
    have edgeIndexEq :
        crossingRoute.1.2 = edgeIndex := by
      rw [← crossingRoleIndex, ← endpointRoleIndex]
      exact congrArg SegmentRole.edgeIndex rolesEqual
    have taggedEdgeEq :
        crossingRoute.1 = (edge, edgeIndex) :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        crossingEdgeMem edgeMem edgeIndexEq
    rw [taggedEdgeEq] at crossingClassifiedMem
    have taggedClassifiedEq :
        crossingClassified = classified :=
      taggedClassified_eq_of_role_eq
        crossingClassifiedMem classifiedMem rolesEqual
    rw [taggedClassifiedEq] at crossingContains
    have edgeLocal :
        edge.span ≤ 1 :=
      isLocal edge (List.fst_mem_of_mem_zipIdx edgeMem)
    have span :=
      classifiedSegment_horizontal_span_le_period
        wellFormed degree edgeMem edgeLocal
        (List.fst_mem_of_mem_zipIdx classifiedMem)
        horizontal
    apply
      horizontalSegment_translate_not_interiorContains_endpoint
        horizontal periodPositive span.1 span.2 endpoint
        crossing.firstTranslate translate
    rw [pointEq] at crossingContains
    simpa [PeriodicGridDrawing.periodTranslation,
      drawing_gridSize] using crossingContains
  · have crossingNotEven :=
      horizontalFanout_interior_point_not_even
        degree crossingEdgeMem crossingClassifiedListMem
        crossingFanout crossing.firstTranslate crossing.point
        crossingContains
    have endpointEven :=
      horizontalFanout_translated_endpoints_even
        (List.fst_mem_of_mem_zipIdx classifiedMem)
        endpointFanout translate
    apply crossingNotEven
    rw [pointEq]
    cases endpoint with
    | start =>
        simpa [GridSegment.translate] using endpointEven.1
    | finish =>
        simpa [GridSegment.translate] using endpointEven.2

/-- A retained crossover center cannot coincide with the center of any
enumerated route bend. -/
theorem orientedCrossing_point_ne_drawingRouteBend_drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    crossing.point ≠ routeBend.drawingPoint graph := by
  intro pointEq
  rcases drawingRouteBend_adjacentClassifiedSegments
      graph routeBendMem with
    ⟨edge, edgeIndex, incoming, outgoing,
      edgeMem, incomingMem, outgoingMem,
      routeIndexEq, incomingIndexEq, outgoingIndexEq,
      incomingSegmentEq, outgoingSegmentEq⟩
  have geometry :=
    drawingRouteBend_cornerGeometry
      wellFormed degree isLocal routeBendMem
  rcases geometry.incomingAligned with
    incomingHorizontal | incomingVertical
  · have incomingHorizontal' :
        incoming.1.segment.IsHorizontal := by
      rw [incomingSegmentEq]
      exact incomingHorizontal
    apply
      orientedCrossing_point_ne_horizontal_classified_endpoint
        wellFormed degree isLocal crossingMem
        edgeMem incomingMem incomingHorizontal'
        routeBend.translate .finish
    rw [incomingSegmentEq]
    simpa [RouteBend.drawingPoint] using pointEq
  · rcases geometry.outgoingAligned with
      outgoingHorizontal | outgoingVertical
    · have outgoingHorizontal' :
          outgoing.1.segment.IsHorizontal := by
        rw [outgoingSegmentEq]
        exact outgoingHorizontal
      apply
        orientedCrossing_point_ne_horizontal_classified_endpoint
          wellFormed degree isLocal crossingMem
          edgeMem outgoingMem outgoingHorizontal'
          routeBend.translate .start
      rw [outgoingSegmentEq]
      simpa [RouteBend.drawingPoint] using pointEq
    · have incomingVertical' :
          incoming.1.segment.IsVertical := by
        rw [incomingSegmentEq]
        exact incomingVertical
      have outgoingVertical' :
          outgoing.1.segment.IsVertical := by
        rw [outgoingSegmentEq]
        exact outgoingVertical
      rcases drawingRouteBend_centerPlacement
          graph isLocal routeBendMem with
        ⟨placementEdge, placementEdgeIndex,
          placement, placementIndex,
          placementEdgeMem, placementMem,
          placementRouteIndexEq, placementIndexEq,
          placementPointEq⟩
      have edgeIndexEq :
          placementEdgeIndex = edgeIndex := by
        rw [← placementRouteIndexEq, ← routeIndexEq]
      have taggedEdgeEq :
          (placementEdge, placementEdgeIndex) =
            (edge, edgeIndex) :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          placementEdgeMem edgeMem edgeIndexEq
      have placementEdgeEq :
          placementEdge = edge :=
        congrArg Prod.fst taggedEdgeEq
      subst placementEdge
      rw [edgeIndexEq] at placementMem
      have incomingPlacementIndexEq :
          incoming.2 = placementIndex := by
        omega
      have outgoingPlacementIndexEq :
          outgoing.2 = placementIndex + 1 := by
        omega
      rcases
          routeBendCenterPlacement_kind_port_of_adjacent_vertical
            graph edge edgeIndex placementMem
            incomingMem outgoingMem
            incomingPlacementIndexEq
            outgoingPlacementIndexEq
            incomingVertical' outgoingVertical' with
        ⟨port, placementKindEq⟩
      apply
        orientedCrossing_point_snd_ne_portRow crossingMem
          (Cell.add routeBend.translate placement.offset).2
      have pointYEq :=
        congrArg Prod.snd (pointEq.trans placementPointEq)
      rw [placementKindEq] at pointYEq
      simpa [RouteBendCenterKind.position,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale] using pointYEq

set_option maxRecDepth 4000 in
/-- A retained crossover center cannot coincide with any lifted declared
graph-vertex position. -/
theorem orientedCrossing_point_ne_liftedVertexPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices)
    (vertexTranslate : Cell) :
    crossing.point ≠
      Cell.add
        ((drawing graph).vertexPosition graph vertex)
        ((drawing graph).periodTranslation vertexTranslate) := by
  intro pointEqual
  have sound := orientedCrossingHalo_sound graph crossingMem
  rcases exists_classifiedSegment_of_drawing_mem
      sound.1 with
    ⟨taggedRoute, taggedRouteMem,
      taggedClassified, taggedClassifiedMem, firstEq⟩
  have edgeMem :
      taggedRoute.1 ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx taggedRouteMem
  have classifiedMem :
      taggedClassified.1 ∈
        classifiedRouteSegments graph
          taggedRoute.1.1 taggedRoute.1.2 :=
    List.fst_mem_of_mem_zipIdx taggedClassifiedMem
  have translatedHorizontal :
      (taggedClassified.1.segment.translate
        ((drawing graph).periodTranslation
          crossing.firstTranslate)).IsHorizontal := by
    simpa [CrossingRecord.firstSegment, firstEq] using
      sound.2.2.2.2.2.1
  have storedHorizontal :
      taggedClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp
      translatedHorizontal
  have horizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      classifiedMem storedHorizontal
  have translatedContains :
      (taggedClassified.1.segment.translate
        ((drawing graph).periodTranslation
          crossing.firstTranslate)).InteriorContains
        crossing.point := by
    simpa [CrossingRecord.firstSegment, firstEq] using
      sound.2.2.2.2.2.2.2.1
  have pointY :
      crossing.point.2 =
        taggedClassified.1.segment.start.2 +
          drawingGridSize graph * crossing.firstTranslate.2 := by
    rcases translatedContains with
      ⟨_horizontal, sameY, _between⟩ |
        ⟨vertical, _sameX, _between⟩
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        drawing_gridSize, Cell.add, Cell.scale,
        add_comm] using sameY
    · exact (translatedHorizontal.2 vertical.1).elim
  have lane :=
    classifiedSegment_horizontal_lane
      classifiedMem horizontalRole
  have pointYBase :
      crossing.point.2 =
        2 + (drawing graph).gridSize * vertexTranslate.2 := by
    rw [pointEqual,
      drawing_vertexPosition_of_mem graph vertexMem]
    simp [PeriodicGridDrawing.periodTranslation,
      vertexPosition, Cell.add, Cell.scale]
  have laneBounds :=
    horizontalLaneBase_bounds edgeMem classifiedMem horizontalRole
  have twoBounds :
      0 ≤ (2 : Int) ∧
        (2 : Int) < (drawing graph).gridSize := by
    rw [drawing_gridSize]
    have sizePositive := drawingGridSize_pos graph
    unfold drawingGridSize at sizePositive ⊢
    omega
  have laneBounds' :
      0 ≤ horizontalLaneBase taggedClassified.1.role ∧
        horizontalLaneBase taggedClassified.1.role <
          (drawing graph).gridSize := by
    simpa [drawing_gridSize] using laneBounds
  have lanePeriodicEqual :
      (2 : Int) +
          (drawing graph).gridSize * vertexTranslate.2 =
        horizontalLaneBase taggedClassified.1.role +
          (drawing graph).gridSize *
            (horizontalLaneCellShift taggedRoute.1.1
              taggedClassified.1.role +
                crossing.firstTranslate.2) := by
    rw [drawing_gridSize]
    rw [lane] at pointY
    rw [pointYBase] at pointY
    simpa [mul_add, add_assoc] using pointY
  have laneBaseEqual :=
    ((drawing graph).translatedHalfOpenCoordinates_eq
      twoBounds laneBounds' lanePeriodicEqual).1
  have fanout :
      taggedClassified.1.role.IsHorizontalFanout := by
    cases roleEq : taggedClassified.1.role with
    | sourceFanoutHorizontal port =>
        simp [SegmentRole.IsHorizontalFanout]
    | sourceFanoutVertical port =>
        simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
    | sourcePortVertical port =>
        simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
    | lowHorizontal roleEdgeIndex =>
        simp [roleEq, horizontalLaneBase, edgeTrack] at laneBaseEqual
        omega
    | highHorizontal roleEdgeIndex =>
        simp [roleEq, horizontalLaneBase, edgeTrack] at laneBaseEqual
        omega
    | gateVertical roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
    | boundaryVertical roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
    | targetPortVertical port =>
        simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
    | targetFanoutVertical port =>
        simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
    | targetFanoutHorizontal port =>
        simp [SegmentRole.IsHorizontalFanout]
  rcases horizontalFanout_midpoint_of_interiorContains
      degree edgeMem classifiedMem fanout
      crossing.firstTranslate crossing.point
      translatedContains with
    ⟨port, portEq, portMem, midpointEqual⟩
  have midpointBounds :=
    fanoutMidpointBase_bounds
      wellFormed degree portEq portMem
  have vertexXBounds := vertexX_bounds vertexMem
  have vertexXBounds' :
      0 ≤ vertexX (graph.vertices.idxOf vertex) ∧
        vertexX (graph.vertices.idxOf vertex) <
          (drawing graph).gridSize := by
    simpa [drawing_gridSize] using
      ⟨le_of_lt vertexXBounds.1, vertexXBounds.2⟩
  have midpointBounds' :
      0 ≤ fanoutMidpointBase graph taggedClassified.1.role ∧
        fanoutMidpointBase graph taggedClassified.1.role <
          (drawing graph).gridSize := by
    simpa [drawing_gridSize] using midpointBounds
  have pointXBase :
      crossing.point.1 =
        vertexX (graph.vertices.idxOf vertex) +
          (drawing graph).gridSize * vertexTranslate.1 := by
    rw [pointEqual,
      drawing_vertexPosition_of_mem graph vertexMem]
    simp [PeriodicGridDrawing.periodTranslation,
      vertexPosition, Cell.add, Cell.scale]
  have midpointPeriodicEqual :
      vertexX (graph.vertices.idxOf vertex) +
          (drawing graph).gridSize * vertexTranslate.1 =
        fanoutMidpointBase graph taggedClassified.1.role +
          (drawing graph).gridSize *
            ((horizontalFanoutCellShift taggedRoute.1.1
              taggedClassified.1.role).1 +
                crossing.firstTranslate.1) := by
    rw [drawing_gridSize]
    rw [pointXBase] at midpointEqual
    cases roleEq : taggedClassified.1.role with
    | sourceFanoutHorizontal rolePort =>
        have rolePortEq : rolePort = port := by
          simpa [roleEq,
            SegmentRole.horizontalFanoutPort] using portEq
        subst port
        simpa [roleEq, fanoutMidpointBase,
          horizontalFanoutCellShift, mul_add,
          add_assoc] using midpointEqual
    | sourceFanoutVertical rolePort =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | sourcePortVertical rolePort =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | lowHorizontal roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | highHorizontal roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | gateVertical roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | boundaryVertical roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | targetPortVertical rolePort =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | targetFanoutVertical rolePort =>
        simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
    | targetFanoutHorizontal rolePort =>
        have rolePortEq : rolePort = port := by
          simpa [roleEq,
            SegmentRole.horizontalFanoutPort] using portEq
        subst port
        simpa [roleEq, fanoutMidpointBase,
          horizontalFanoutCellShift, mul_add,
          add_assoc] using midpointEqual
  have midpointBaseEqual :=
    ((drawing graph).translatedHalfOpenCoordinates_eq
      vertexXBounds' midpointBounds' midpointPeriodicEqual).1
  exact
    (classifiedSegment_horizontalFanout_midpoint_ne_vertexX
      degree classifiedMem fanout portEq portMem)
      midpointBaseEqual

end PeriodicOrthocrossing
end LeanTrominoes
