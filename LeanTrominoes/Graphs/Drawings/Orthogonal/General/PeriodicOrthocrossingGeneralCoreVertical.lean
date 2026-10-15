/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreHorizontal
import LeanTrominoes.Graphs.Drawings.Orthogonal.Vertical.PeriodicOrthocrossingVertical

/-! # Vertical columns, including boundary detours, in the general construction -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def gateX {Vertex : Type*} (graph : PeriodicGraph Vertex) (index : Nat) : Int :=
  3*graph.vertices.length+2*graph.edges.length+4+2*index

def verticalBase {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : SegmentRole Vertex → Int
  | .sourcePortVertical port | .targetPortVertical port => portX graph port
  | .gateVertical index => gateX graph index
  | _ => 0

def verticalShift {Vertex : Type*} (edge : PeriodicEdge Vertex) : SegmentRole Vertex → Int
  | .targetPortVertical _ => edge.offset.1
  | .boundaryVertical _ => max edge.offset.1 0
  | _ => 0

theorem classifiedCore_vertical_role {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.segment.IsVertical →
      piece.role.IsActiveVertical ∨ piece.role = .boundaryVertical index := by
  unfold classifiedCore
  split <;> simp_all [GridSegment.IsVertical,SegmentRole.IsActiveVertical,Cell.add,Cell.scale]
  all_goals split <;> simp_all [GridSegment.IsVertical,SegmentRole.IsActiveVertical,Cell.add,Cell.scale]
  all_goals omega

theorem classifiedCore_vertical_column {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat)
    (edgeLocal : edge.span ≤ 1) :
    ∀ piece ∈ classifiedCore graph edge index, piece.segment.IsVertical →
      piece.segment.start.1 = verticalBase graph piece.role+
        (drawingGridSize graph : Int)*verticalShift edge piece.role := by
  rcases offset_eq_of_span_le_one edge edgeLocal with offset | offset | offset | offset | offset
  all_goals simp [classifiedCore,offset,GridSegment.IsVertical,verticalBase,verticalShift,
    gateX,Cell.add,Cell.scale]
  all_goals try split
  all_goals try simp_all [GridSegment.IsVertical,verticalBase,verticalShift,gateX,Cell.add,Cell.scale]
  all_goals omega

theorem classifiedCore_activePort_mem {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) :
    ∀ piece ∈ classifiedCore graph tagged.1 tagged.2,
      ∀ port, piece.role.activeVerticalPort = some port → port ∈ allPorts graph := by
  have source := sourcePort_mem_allPorts graph member
  have target := targetPort_mem_allPorts graph member
  unfold classifiedCore
  split <;> simp_all [SegmentRole.activeVerticalPort]
  all_goals split <;> simp_all [SegmentRole.activeVerticalPort]

theorem classifiedCore_activeEnd_correct {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.role.ActiveVerticalEndCorrect := by
  unfold classifiedCore
  split <;> simp_all [SegmentRole.ActiveVerticalEndCorrect,sourcePort,targetPort]
  all_goals split <;> simp_all [SegmentRole.ActiveVerticalEndCorrect,sourcePort,targetPort]

theorem classifiedCore_vertical_base_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    ∀ piece ∈ classifiedCore graph tagged.1 tagged.2, piece.segment.IsVertical →
      0 ≤ verticalBase graph piece.role ∧ verticalBase graph piece.role < drawingGridSize graph := by
  have source := portX_lt_gridSize wellFormed (sourcePort_mem_allPorts graph member)
  have target := portX_lt_gridSize wellFormed (targetPort_mem_allPorts graph member)
  have valid : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  unfold classifiedCore
  split <;> simp_all [GridSegment.IsVertical,verticalBase,gateX,Cell.add,Cell.scale,drawingGridSize]
  all_goals try split
  all_goals try simp_all [GridSegment.IsVertical,verticalBase,gateX,Cell.add,Cell.scale,drawingGridSize]
  all_goals omega

theorem active_vertical_roles_eq_of_bases_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {first second : SegmentRole Vertex}
    (firstActive : first.IsActiveVertical) (secondActive : second.IsActiveVertical)
    (firstEnd : first.ActiveVerticalEndCorrect) (secondEnd : second.ActiveVerticalEndCorrect)
    (firstMember : ∀ port, first.activeVerticalPort = some port → port ∈ allPorts graph)
    (secondMember : ∀ port, second.activeVerticalPort = some port → port ∈ allPorts graph)
    (sameBase : verticalBase graph first = verticalBase graph second) : first = second := by
  cases first <;> cases second <;>
    simp_all [SegmentRole.IsActiveVertical,SegmentRole.ActiveVerticalEndCorrect,
      SegmentRole.activeVerticalPort,verticalBase]
  all_goals first
    | have equal := portX_injective wellFormed (by assumption) (by assumption) sameBase
      subst_vars
      simp_all
    | have bounds := portX_bounds wellFormed (by assumption)
      unfold gateX at sameBase
      omega
    | unfold gateX at sameBase
      congr 1
      omega

theorem classifiedCore_active_base_positive {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    (active : piece.role.IsActiveVertical) : 0 < verticalBase graph piece.role := by
  have portMember := classifiedCore_activePort_mem member piece pieceMember
  cases roleEq : piece.role <;> simp_all [SegmentRole.IsActiveVertical,verticalBase,
    SegmentRole.activeVerticalPort,gateX]
  all_goals first | omega | exact (portX_bounds wellFormed (by assumption)).1

theorem classifiedCore_boundary_bounds {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, piece.role = .boundaryVertical index →
      piece.segment.start.2 = edgeTrack index ∧ piece.segment.finish.2 = edgeTrack index+1 := by
  unfold classifiedCore
  split <;> simp_all
  all_goals split <;> simp_all

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
