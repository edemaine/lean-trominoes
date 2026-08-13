/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingClassification
import Mathlib.Tactic.Linarith

/-!
# Horizontal private lanes in the periodic track construction

Horizontal fanouts occupy row `2`, while protoedge `i` owns rows `6 + 4i`
and `7 + 4i`.  Rows outside the stored square are normalized by recording
the corresponding cell shift.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Exactly the four roles represented by horizontal segments. -/
def SegmentRole.IsHorizontalRole {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourceFanoutHorizontal _
  | .targetFanoutHorizontal _
  | .lowHorizontal _
  | .highHorizontal _ => True
  | _ => False

/-- The two horizontal roles belonging to the short fanout around a vertex. -/
def SegmentRole.IsHorizontalFanout {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourceFanoutHorizontal _
  | .targetFanoutHorizontal _ => True
  | _ => False

/-- Port named by a horizontal fanout role. -/
def SegmentRole.horizontalFanoutPort {Vertex : Type*} :
    SegmentRole Vertex → Option (GraphPort Vertex)
  | .sourceFanoutHorizontal port
  | .targetFanoutHorizontal port => some port
  | _ => none

/-- The unique integer point in the interior of a length-two fanout segment,
represented in the fundamental drawing square. -/
def fanoutMidpointBase {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : SegmentRole Vertex → Int
  | .sourceFanoutHorizontal port
  | .targetFanoutHorizontal port =>
      vertexX (graph.vertices.idxOf port.vertex) +
        (portRank graph port : Int) - 1
  | _ => 0

/-- Whole-cell correction already stored in a classified fanout segment. -/
def horizontalFanoutCellShift {Vertex : Type*}
    (edge : PeriodicEdge Vertex) : SegmentRole Vertex → Cell
  | .targetFanoutHorizontal _ => edge.offset
  | _ => (0, 0)

instance {Vertex : Type*} (role : SegmentRole Vertex) :
    Decidable role.IsHorizontalRole := by
  cases role <;> unfold SegmentRole.IsHorizontalRole <;> infer_instance

/-- Any classified segment that is geometrically horizontal has one of the
four horizontal semantic roles. -/
theorem classifiedSegment_horizontalRole_of_isHorizontal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.segment.IsHorizontal) :
    classified.role.IsHorizontalRole := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsHorizontal → item.role.IsHorizontalRole := by
    simp [classifiedSourceFanout, SegmentRole.IsHorizontalRole,
      GridSegment.IsHorizontal]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsHorizontal → item.role.IsHorizontalRole := by
    simp [classifiedEdgeCore, SegmentRole.IsHorizontalRole,
      GridSegment.IsHorizontal, Cell.add, Cell.scale]
    split <;> simp_all
    all_goals split <;> simp_all
    all_goals simp_all [add_comm, sub_eq_add_neg]
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsHorizontal → item.role.IsHorizontalRole := by
    simp [classifiedTargetFanout, SegmentRole.IsHorizontalRole,
      GridSegment.IsHorizontal, Cell.add, Cell.scale]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem => sourceAll classified sourceMem horizontal)
      (fun coreMem => coreAll classified coreMem horizontal))
    (fun targetMem => targetAll classified targetMem horizontal)

/-- Fundamental-square representative of a horizontal lane. -/
def horizontalLaneBase {Vertex : Type*} :
    SegmentRole Vertex → Int
  | .sourceFanoutHorizontal _
  | .targetFanoutHorizontal _ => 2
  | .lowHorizontal edgeIndex => edgeTrack edgeIndex
  | .highHorizontal edgeIndex => edgeTrack edgeIndex + 1
  | _ => 0

/-- Cell correction used to normalize a stored horizontal lane. -/
def horizontalLaneCellShift {Vertex : Type*}
    (edge : PeriodicEdge Vertex) : SegmentRole Vertex → Int
  | .targetFanoutHorizontal _ => edge.offset.2
  | .lowHorizontal _ =>
      if edge.offset = (0, 1) then 1 else 0
  | .highHorizontal _ =>
      if edge.offset = (0, -1) then -1 else 0
  | _ => 0

/-- A classified horizontal segment's stored row is its fundamental lane plus
the recorded whole-cell correction. -/
theorem classifiedSegment_horizontal_lane {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.role.IsHorizontalRole) :
    classified.segment.start.2 =
      horizontalLaneBase classified.role +
        drawingGridSize graph *
          horizontalLaneCellShift edge classified.role := by
  have all :
      ∀ item ∈ classifiedRouteSegments graph edge edgeIndex,
        item.role.IsHorizontalRole →
        item.segment.start.2 =
          horizontalLaneBase item.role +
            drawingGridSize graph *
              horizontalLaneCellShift edge item.role := by
    let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
    let targetCenter := vertexX (graph.vertices.idxOf edge.target)
    let sourceColumn := portX graph (sourcePort edge edgeIndex)
    let targetColumn := portX graph (targetPort edge edgeIndex)
    by_cases sourceSame : sourceCenter = sourceColumn <;>
      by_cases targetSame : targetCenter = targetColumn <;>
      simp [classifiedRouteSegments, classifiedSourceFanout,
        classifiedEdgeCore, classifiedTargetFanout,
        SegmentRole.IsHorizontalRole, horizontalLaneBase,
        horizontalLaneCellShift, sourceCenter, targetCenter,
        sourceColumn, targetColumn, sourceSame, targetSame,
        Cell.add, Cell.scale]
    all_goals split <;> simp_all
    all_goals try aesop
    all_goals simp_all [add_comm]
  exact all classified classifiedMem horizontal

/-- Every real horizontal lane representative lies strictly inside one
drawing period. -/
theorem horizontalLaneBase_bounds {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.role.IsHorizontalRole) :
    0 ≤ horizontalLaneBase classified.role ∧
      horizontalLaneBase classified.role < drawingGridSize graph := by
  have roleIndex :=
    classifiedSegment_role_edgeIndex classifiedMem
  have tracks := edgeTrack_bounds graph edgeMem
  have sizePositive := drawingGridSize_pos graph
  cases roleEq : classified.role <;>
    simp_all [SegmentRole.IsHorizontalRole, horizontalLaneBase,
      SegmentRole.edgeIndex, edgeTrack] <;>
    omega

/-- Equal horizontal lane representatives identify the same private-track
role, unless both roles are fanout pieces on the shared fanout row. -/
theorem horizontal_roles_eq_or_both_fanout {Vertex : Type*}
    {first second : SegmentRole Vertex}
    (firstHorizontal : first.IsHorizontalRole)
    (secondHorizontal : second.IsHorizontalRole)
    (lanesEqual :
      horizontalLaneBase first = horizontalLaneBase second) :
    first = second ∨
      (first.IsHorizontalFanout ∧ second.IsHorizontalFanout) := by
  cases first <;> cases second <;>
    simp_all [SegmentRole.IsHorizontalRole,
      SegmentRole.IsHorizontalFanout, horizontalLaneBase, edgeTrack] <;>
    omega

/-- Fanout midpoints are unique representatives of real ports modulo one
drawing period. -/
theorem fanoutMidpointBase_bounds {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {role : SegmentRole Vertex} {port : GraphPort Vertex}
    (portEq : role.horizontalFanoutPort = some port)
    (portMem : port ∈ allPorts graph) :
    0 ≤ fanoutMidpointBase graph role ∧
      fanoutMidpointBase graph role < drawingGridSize graph := by
  have vertexMem := port_vertex_mem wellFormed portMem
  have vertexIndexLt :
      graph.vertices.idxOf port.vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMem
  have rankLt := portRank_lt_three degree portMem
  cases role <;>
    simp_all [SegmentRole.horizontalFanoutPort, fanoutMidpointBase,
      vertexX, drawingGridSize] <;>
    omega

/-- Two real ports with the same fanout midpoint representative are equal. -/
theorem horizontalFanoutPort_eq_of_midpoint_eq {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {firstRole secondRole : SegmentRole Vertex}
    {firstPort secondPort : GraphPort Vertex}
    (firstPortEq :
      firstRole.horizontalFanoutPort = some firstPort)
    (secondPortEq :
      secondRole.horizontalFanoutPort = some secondPort)
    (firstMem : firstPort ∈ allPorts graph)
    (secondMem : secondPort ∈ allPorts graph)
    (midpointsEqual :
      fanoutMidpointBase graph firstRole =
        fanoutMidpointBase graph secondRole) :
    firstPort = secondPort := by
  have firstRank := portRank_lt_three degree firstMem
  have secondRank := portRank_lt_three degree secondMem
  have firstVertexMem := port_vertex_mem wellFormed firstMem
  have secondVertexMem := port_vertex_mem wellFormed secondMem
  have firstVertexIndexLt :
      graph.vertices.idxOf firstPort.vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr firstVertexMem
  have secondVertexIndexLt :
      graph.vertices.idxOf secondPort.vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr secondVertexMem
  have columnsEqual :
      portX graph firstPort = portX graph secondPort := by
    cases firstRole <;> cases secondRole <;>
      simp_all [SegmentRole.horizontalFanoutPort, fanoutMidpointBase,
        portX, vertexX] <;>
      omega
  exact portX_injective_on_allPorts
    wellFormed degree firstMem secondMem columnsEqual

/-- Every horizontal piece of a local route has horizontal span at most one
drawing period, in either endpoint order. -/
theorem classifiedSegment_horizontal_span_le_period
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    (edgeLocal : edge.span ≤ 1)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.segment.IsHorizontal) :
    classified.segment.finish.1 - classified.segment.start.1 ≤
        drawingGridSize graph ∧
      classified.segment.start.1 - classified.segment.finish.1 ≤
        drawingGridSize graph := by
  have sourceMem :=
    sourcePort_mem_allPorts graph edgeMem
  have targetMem :=
    targetPort_mem_allPorts graph edgeMem
  have sourceBounds :=
    portX_bounds wellFormed degree sourceMem
  have targetBounds :=
    portX_bounds wellFormed degree targetMem
  have sourceRank :=
    portRank_lt_three degree sourceMem
  have targetRank :=
    portRank_lt_three degree targetMem
  have gateBounds := edgeGateX_bounds graph edgeMem
  have periodPositive := drawingGridSize_pos graph
  have sourceBounds' :
      0 < portX graph (sourcePort edge edgeIndex) ∧
        portX graph (sourcePort edge edgeIndex) <
          drawingGridSize graph := by
    simpa using sourceBounds
  have targetBounds' :
      0 < portX graph (targetPort edge edgeIndex) ∧
        portX graph (targetPort edge edgeIndex) <
          drawingGridSize graph := by
    simpa using targetBounds
  have gateBounds' :
      0 < edgeGateX graph edgeIndex ∧
        edgeGateX graph edgeIndex < drawingGridSize graph := by
    simpa using gateBounds
  have sourceRank' :
      portRank graph (sourcePort edge edgeIndex) < 3 := by
    simpa using sourceRank
  have targetRank' :
      portRank graph (targetPort edge edgeIndex) < 3 := by
    simpa using targetRank
  have sourcePortX :
      portX graph (sourcePort edge edgeIndex) =
        vertexX (graph.vertices.idxOf edge.source) +
          2 * (portRank graph (sourcePort edge edgeIndex) : Int) - 2 := by
    rfl
  have targetPortX :
      portX graph (targetPort edge edgeIndex) =
        vertexX (graph.vertices.idxOf edge.target) +
          2 * (portRank graph (targetPort edge edgeIndex) : Int) - 2 := by
    rfl
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsHorizontal →
          item.segment.finish.1 - item.segment.start.1 ≤
              drawingGridSize graph ∧
            item.segment.start.1 - item.segment.finish.1 ≤
              drawingGridSize graph := by
    intro item itemMem itemHorizontal
    by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at itemMem
      subst item
      simp [GridSegment.IsHorizontal] at itemHorizontal
    · simp [classifiedSourceFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp only [ClassifiedSegment.segment, GridSegment.finish,
          GridSegment.start]
        omega
      · simp [GridSegment.IsHorizontal] at itemHorizontal
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsHorizontal →
          item.segment.finish.1 - item.segment.start.1 ≤
              drawingGridSize graph ∧
            item.segment.start.1 - item.segment.finish.1 ≤
              drawingGridSize graph := by
    rcases offset_eq_of_span_le_one edge edgeLocal with
      offsetZero | offsetRight | offsetLeft | offsetUp | offsetDown
    · simp [classifiedEdgeCore, offsetZero,
        GridSegment.IsHorizontal, Cell.add, Cell.scale]
      omega
    · simp [classifiedEdgeCore, offsetRight,
        GridSegment.IsHorizontal, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    · simp [classifiedEdgeCore, offsetLeft,
        GridSegment.IsHorizontal, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    · simp [classifiedEdgeCore, offsetUp,
        GridSegment.IsHorizontal, Cell.add, Cell.scale]
      omega
    · simp [classifiedEdgeCore, offsetDown,
        GridSegment.IsHorizontal, Cell.add, Cell.scale]
      omega
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsHorizontal →
          item.segment.finish.1 - item.segment.start.1 ≤
              drawingGridSize graph ∧
            item.segment.start.1 - item.segment.finish.1 ≤
              drawingGridSize graph := by
    intro item itemMem itemHorizontal
    by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at itemMem
      subst item
      simp [GridSegment.IsHorizontal, Cell.add, Cell.scale]
        at itemHorizontal
    · simp [classifiedTargetFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [GridSegment.IsHorizontal, Cell.add, Cell.scale]
          at itemHorizontal
      · simp only [ClassifiedSegment.segment, GridSegment.finish,
          GridSegment.start, Cell.add, Cell.scale]
        omega
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceClassified =>
        sourceAll classified sourceClassified horizontal)
      (fun coreClassified =>
        coreAll classified coreClassified horizontal))
    (fun targetClassified =>
      targetAll classified targetClassified horizontal)

/-- Horizontal interior containment exposes strict containment of the point's
horizontal coordinate between the segment endpoints. -/
theorem strictlyBetween_x_of_interiorContains_of_isHorizontal
    {segment : GridSegment} {point : Cell}
    (contains : segment.InteriorContains point)
    (horizontal : segment.IsHorizontal) :
    GridSegment.StrictlyBetween
      segment.start.1 segment.finish.1 point.1 := by
  rcases contains with
    ⟨_, _, between⟩ | ⟨vertical, _, _⟩
  · exact between
  · simp [GridSegment.IsHorizontal, GridSegment.IsVertical]
      at horizontal vertical
    omega

theorem strictlyBetween_symm {first last value : Int}
    (contains : GridSegment.StrictlyBetween first last value) :
    GridSegment.StrictlyBetween last first value := by
  unfold GridSegment.StrictlyBetween at contains ⊢
  exact contains.elim Or.inr Or.inl

/-- A noncentral rank-zero or rank-two port lies two columns from its vertex
center, so its horizontal fanout has exactly one integer interior point. -/
theorem strictlyBetween_fanout_midpoint
    {center period shift point : Int} {rank : Nat}
    (rankCase : rank = 0 ∨ rank = 2)
    (contains :
      GridSegment.StrictlyBetween
        (center + period * shift)
        (center + 2 * (rank : Int) - 2 + period * shift)
        point) :
    point = center + (rank : Int) - 1 + period * shift := by
  rcases rankCase with rfl | rfl <;>
    unfold GridSegment.StrictlyBetween at contains <;>
    rcases contains with contains | contains <;>
    omega

/-- A common point in a horizontal fanout interior is its unique midpoint,
with both the edge's stored cell correction and the occurrence translation
made explicit. -/
theorem horizontalFanout_midpoint_of_interiorContains
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
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
    ∃ port,
        classified.role.horizontalFanoutPort = some port ∧
        port ∈ allPorts graph ∧
        point.1 =
          vertexX (graph.vertices.idxOf port.vertex) +
            (portRank graph port : Int) - 1 +
            drawingGridSize graph *
              (horizontalFanoutCellShift edge classified.role).1 +
            drawingGridSize graph * translate.1 := by
  have sourceMem := sourcePort_mem_allPorts graph edgeMem
  have targetMem := targetPort_mem_allPorts graph edgeMem
  have sourceRank := portRank_lt_three degree sourceMem
  have targetRank := portRank_lt_three degree targetMem
  have sourceRank' :
      portRank graph (sourcePort edge edgeIndex) < 3 := by
    simpa using sourceRank
  have targetRank' :
      portRank graph (targetPort edge edgeIndex) < 3 := by
    simpa using targetRank
  have sourcePortX :
      portX graph (sourcePort edge edgeIndex) =
        vertexX (graph.vertices.idxOf edge.source) +
          2 * (portRank graph (sourcePort edge edgeIndex) : Int) - 2 := by
    rfl
  have targetPortX :
      portX graph (targetPort edge edgeIndex) =
        vertexX (graph.vertices.idxOf edge.target) +
          2 * (portRank graph (targetPort edge edgeIndex) : Int) - 2 := by
    rfl
  have sourceVertexX :
      vertexX
          (graph.vertices.idxOf (sourcePort edge edgeIndex).vertex) =
        vertexX (graph.vertices.idxOf edge.source) := by
    rfl
  have targetVertexX :
      vertexX
          (graph.vertices.idxOf (targetPort edge edgeIndex).vertex) =
        vertexX (graph.vertices.idxOf edge.target) := by
    rfl
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.IsHorizontalFanout →
          (item.segment.translate
            ((drawing graph).periodTranslation translate)).InteriorContains
              point →
          ∃ port,
            item.role.horizontalFanoutPort = some port ∧
              port ∈ allPorts graph ∧
              point.1 =
                vertexX (graph.vertices.idxOf port.vertex) +
                  (portRank graph port : Int) - 1 +
                  drawingGridSize graph *
                    (horizontalFanoutCellShift edge item.role).1 +
                  drawingGridSize graph * translate.1 := by
    intro item itemMem itemFanout itemContains
    by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at itemMem
      subst item
      simp [SegmentRole.IsHorizontalFanout] at itemFanout
    · simp [classifiedSourceFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · refine ⟨sourcePort edge edgeIndex, rfl, sourceMem, ?_⟩
        have sourceRankCase :
            portRank graph (sourcePort edge edgeIndex) = 0 ∨
              portRank graph (sourcePort edge edgeIndex) = 2 := by
          omega
        have storedHorizontal :
            (GridSegment.mk
              (vertexX (graph.vertices.idxOf edge.source), 2)
              (portX graph (sourcePort edge edgeIndex), 2)).IsHorizontal :=
          ⟨rfl, same⟩
        have translatedHorizontal :
            ((GridSegment.mk
              (vertexX (graph.vertices.idxOf edge.source), 2)
              (portX graph (sourcePort edge edgeIndex), 2)).translate
                ((drawing graph).periodTranslation translate)).IsHorizontal :=
          (GridSegment.isHorizontal_translate _ _).mpr storedHorizontal
        have between :=
          strictlyBetween_x_of_interiorContains_of_isHorizontal
            itemContains translatedHorizontal
        have between' :
            GridSegment.StrictlyBetween
              (vertexX (graph.vertices.idxOf edge.source) +
                drawingGridSize graph * translate.1)
              (vertexX (graph.vertices.idxOf edge.source) +
                2 * (portRank graph
                  (sourcePort edge edgeIndex) : Int) - 2 +
                drawingGridSize graph * translate.1)
              point.1 := by
          simpa [GridSegment.translate,
            PeriodicGridDrawing.periodTranslation, drawing_gridSize,
            Cell.add, Cell.scale, sourcePortX, add_comm, add_left_comm,
            add_assoc] using between
        have midpoint :=
          strictlyBetween_fanout_midpoint sourceRankCase between'
        simpa [horizontalFanoutCellShift, sourceVertexX] using midpoint
      · simp [SegmentRole.IsHorizontalFanout] at itemFanout
  have coreNone :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        ¬item.role.IsHorizontalFanout := by
    simp [classifiedEdgeCore, SegmentRole.IsHorizontalFanout]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.IsHorizontalFanout →
          (item.segment.translate
            ((drawing graph).periodTranslation translate)).InteriorContains
              point →
          ∃ port,
            item.role.horizontalFanoutPort = some port ∧
              port ∈ allPorts graph ∧
              point.1 =
                vertexX (graph.vertices.idxOf port.vertex) +
                  (portRank graph port : Int) - 1 +
                  drawingGridSize graph *
                    (horizontalFanoutCellShift edge item.role).1 +
                  drawingGridSize graph * translate.1 := by
    intro item itemMem itemFanout itemContains
    by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at itemMem
      subst item
      simp [SegmentRole.IsHorizontalFanout] at itemFanout
    · simp [classifiedTargetFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [SegmentRole.IsHorizontalFanout] at itemFanout
      · refine ⟨targetPort edge edgeIndex, rfl, targetMem, ?_⟩
        have targetRankCase :
            portRank graph (targetPort edge edgeIndex) = 0 ∨
              portRank graph (targetPort edge edgeIndex) = 2 := by
          omega
        let edgeTranslate :=
          Cell.scale (drawingGridSize graph : Int) edge.offset
        have storedHorizontal :
            (GridSegment.mk
              (Cell.add edgeTranslate
                (portX graph (targetPort edge edgeIndex), 2))
              (Cell.add edgeTranslate
                (vertexX (graph.vertices.idxOf edge.target), 2))).IsHorizontal := by
          simp [GridSegment.IsHorizontal, edgeTranslate, Cell.add, Cell.scale]
          exact Ne.symm same
        have translatedHorizontal :
            ((GridSegment.mk
              (Cell.add edgeTranslate
                (portX graph (targetPort edge edgeIndex), 2))
              (Cell.add edgeTranslate
                (vertexX (graph.vertices.idxOf edge.target), 2))).translate
                  ((drawing graph).periodTranslation translate)).IsHorizontal :=
          (GridSegment.isHorizontal_translate _ _).mpr storedHorizontal
        have between :=
          strictlyBetween_x_of_interiorContains_of_isHorizontal
            itemContains translatedHorizontal
        have between' :
            GridSegment.StrictlyBetween
              (vertexX (graph.vertices.idxOf edge.target) +
                drawingGridSize graph *
                  (edge.offset.1 + translate.1))
              (vertexX (graph.vertices.idxOf edge.target) +
                2 * (portRank graph
                  (targetPort edge edgeIndex) : Int) - 2 +
                drawingGridSize graph *
                  (edge.offset.1 + translate.1))
              point.1 := by
          apply strictlyBetween_symm
          simpa [GridSegment.translate,
            PeriodicGridDrawing.periodTranslation, drawing_gridSize,
            edgeTranslate, Cell.add, Cell.scale, targetPortX, mul_add,
            add_comm, add_left_comm, add_assoc] using between
        have midpoint :=
          strictlyBetween_fanout_midpoint targetRankCase between'
        simpa [horizontalFanoutCellShift, targetVertexX, mul_add,
          add_comm, add_left_comm, add_assoc] using midpoint
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceClassified =>
        sourceAll classified sourceClassified fanout contains)
      (fun coreClassified =>
        (coreNone classified coreClassified fanout).elim))
    (fun targetClassified =>
      targetAll classified targetClassified fanout contains)

/-- Open intervals of span at most one period cannot overlap after distinct
integer period translations. -/
theorem strictlyBetween_periodic_shifts_unique
    {period first last firstShift secondShift point : Int}
    (periodPositive : 0 < period)
    (spanForward : last - first ≤ period)
    (spanBackward : first - last ≤ period)
    (firstContains :
      GridSegment.StrictlyBetween
        (first + period * firstShift)
        (last + period * firstShift) point)
    (secondContains :
      GridSegment.StrictlyBetween
        (first + period * secondShift)
        (last + period * secondShift) point) :
    firstShift = secondShift := by
  unfold GridSegment.StrictlyBetween at firstContains secondContains
  rcases firstContains with firstContains | firstContains <;>
    rcases secondContains with secondContains | secondContains <;>
    nlinarith

end PeriodicOrthocrossing
end LeanTrominoes
