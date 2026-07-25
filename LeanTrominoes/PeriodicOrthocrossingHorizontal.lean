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

instance {Vertex : Type*} (role : SegmentRole Vertex) :
    Decidable role.IsHorizontalRole := by
  cases role <;> unfold SegmentRole.IsHorizontalRole <;> infer_instance

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
