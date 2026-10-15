/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreClassification
import LeanTrominoes.Graphs.Drawings.Orthogonal.Horizontal.PeriodicOrthocrossingHorizontal

/-! # Private horizontal rows of the general track construction -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem classifiedCore_role_index {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.role.edgeIndex = index := by
  unfold classifiedCore
  split <;> simp_all [SegmentRole.edgeIndex,sourcePort,targetPort]
  all_goals split <;> simp_all [SegmentRole.edgeIndex,sourcePort,targetPort]

theorem classifiedCore_role_unique {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ first ∈ classifiedCore graph edge index, ∀ second ∈ classifiedCore graph edge index,
      first.role = second.role → first = second := by
  unfold classifiedCore
  split <;> simp_all
  all_goals split <;> simp_all

theorem classifiedCore_horizontal_role {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.segment.IsHorizontal → piece.role.IsHorizontalRole := by
  unfold classifiedCore
  split <;> simp_all [GridSegment.IsHorizontal,SegmentRole.IsHorizontalRole,Cell.add,Cell.scale]
  all_goals split <;> simp_all [GridSegment.IsHorizontal,SegmentRole.IsHorizontalRole,Cell.add,Cell.scale]
  all_goals omega

theorem classifiedCore_horizontal_low_or_high {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.role.IsHorizontalRole →
      piece.role = .lowHorizontal index ∨ piece.role = .highHorizontal index := by
  unfold classifiedCore
  split <;> simp_all [SegmentRole.IsHorizontalRole]
  all_goals split <;> simp_all [SegmentRole.IsHorizontalRole]

theorem classifiedCore_horizontal_lane {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.role.IsHorizontalRole →
      piece.segment.start.2 = horizontalLaneBase piece.role+
        (drawingGridSize graph : Int)*horizontalLaneCellShift edge piece.role := by
  unfold classifiedCore
  split <;> simp_all [SegmentRole.IsHorizontalRole,horizontalLaneBase,horizontalLaneCellShift,Cell.add,Cell.scale]
  all_goals try split
  all_goals try simp_all [SegmentRole.IsHorizontalRole,horizontalLaneBase,horizontalLaneCellShift,Cell.add,Cell.scale]
  all_goals omega

theorem classifiedCore_horizontal_lane_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) {piece : ClassifiedSegment Vertex}
    (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    (horizontal : piece.role.IsHorizontalRole) :
    0 ≤ horizontalLaneBase piece.role ∧ horizontalLaneBase piece.role < drawingGridSize graph := by
  have tracks := edgeTrack_bounds graph member
  rcases classifiedCore_horizontal_low_or_high graph tagged.1 tagged.2 piece pieceMember horizontal with low | high
  · rw [low]
    simp only [horizontalLaneBase]
    omega
  · rw [high]
    simp only [horizontalLaneBase]
    omega

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
