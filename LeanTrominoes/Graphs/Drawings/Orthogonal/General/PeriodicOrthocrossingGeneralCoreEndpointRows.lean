/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreHorizontalContacts

/-! # The endpoints of a core piece lie on its edge's private rows or the port row -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def CoreRow {Vertex : Type*} (graph : PeriodicGraph Vertex) (index : Nat) (y : Int) : Prop :=
  ∃ shift : Int, y = 3+(drawingGridSize graph : Int)*shift ∨
    y = edgeTrack index+(drawingGridSize graph : Int)*shift ∨
    y = edgeTrack index+1+(drawingGridSize graph : Int)*shift

theorem core_point_row {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) (edgeLocal : edge.span ≤ 1) :
    ∀ point ∈ core graph edge index, CoreRow graph index point.2 := by
  rcases offset_eq_of_span_le_one edge edgeLocal with offset | offset | offset | offset | offset
  all_goals intro point member
  all_goals simp [core,offset,Cell.add,Cell.scale] at member
  all_goals try split_ifs at member
  all_goals try simp at member
  all_goals repeat' rcases member with rfl | member
  all_goals try subst point
  all_goals unfold CoreRow
  all_goals first
    | (solve | refine ⟨0,?_⟩; omega)
    | (solve | refine ⟨1,?_⟩; omega)
    | (solve | refine ⟨-1,?_⟩; omega)

theorem classifiedCore_endpoint_rows {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) (edgeLocal : edge.span ≤ 1)
    {piece : ClassifiedSegment Vertex} (member : piece ∈ classifiedCore graph edge index) :
    CoreRow graph index piece.segment.start.2 ∧ CoreRow graph index piece.segment.finish.2 := by
  have segmentMember : piece.segment ∈ gridPolylineSegments (core graph edge index) := by
    rw [← classifiedCore_segments]
    exact List.mem_map.mpr ⟨piece,member,rfl⟩
  have ends := gridPolylineSegments_endpoints_mem segmentMember
  exact ⟨core_point_row graph edge index edgeLocal _ ends.1,
    core_point_row graph edge index edgeLocal _ ends.2⟩

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
