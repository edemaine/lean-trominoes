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

end PeriodicOrthocrossing
end LeanTrominoes
