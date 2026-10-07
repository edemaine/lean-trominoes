/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreSimple

/-! # Every core bend joins one horizontal and one vertical piece -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def CoreJoint {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (index : Nat) (horizontal : Bool) (endpoint : Cell) : Prop :=
  ∃ neighbor ∈ classifiedCore graph edge index,
    (if horizontal then neighbor.segment.IsHorizontal else neighbor.segment.IsVertical) ∧
      (neighbor.segment.start = endpoint ∨ neighbor.segment.finish = endpoint)

def PortRow {Vertex : Type*} (graph : PeriodicGraph Vertex) (y : Int) : Prop :=
  ∃ shift : Int, y = 3+(drawingGridSize graph : Int)*shift

theorem core_horizontal_endpoint_joints {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    ∀ piece ∈ classifiedCore graph tagged.1 tagged.2, piece.segment.IsHorizontal →
      CoreJoint graph tagged.1 tagged.2 false piece.segment.start ∧
        CoreJoint graph tagged.1 tagged.2 false piece.segment.finish := by
  have sourceBounds := portX_lt_gridSize wellFormed (sourcePort_mem_allPorts graph member)
  have targetBounds := portX_lt_gridSize wellFormed (targetPort_mem_allPorts graph member)
  have tracks := edgeTrack_bounds graph member
  have valid : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  have positive : (1 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  rcases offset_eq_of_span_le_one tagged.1 edgeLocal with offset | offset | offset | offset | offset
  all_goals simp [classifiedCore,offset,CoreJoint,GridSegment.IsHorizontal,GridSegment.IsVertical,Cell.add,Cell.scale]
  all_goals try split
  all_goals try simp_all [CoreJoint,GridSegment.IsHorizontal,GridSegment.IsVertical,Cell.add,Cell.scale]
  all_goals omega

theorem core_vertical_endpoint_joints {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    ∀ piece ∈ classifiedCore graph tagged.1 tagged.2, piece.segment.IsVertical →
      (CoreJoint graph tagged.1 tagged.2 true piece.segment.start ∨ PortRow graph piece.segment.start.2) ∧
        (CoreJoint graph tagged.1 tagged.2 true piece.segment.finish ∨ PortRow graph piece.segment.finish.2) := by
  have sourceBounds := portX_lt_gridSize wellFormed (sourcePort_mem_allPorts graph member)
  have targetBounds := portX_lt_gridSize wellFormed (targetPort_mem_allPorts graph member)
  have sourceBeforeGate := portX_bounds wellFormed (sourcePort_mem_allPorts graph member)
  have targetBeforeGate := portX_bounds wellFormed (targetPort_mem_allPorts graph member)
  have different := sourcePortX_ne_targetPortX wellFormed member
  have tracks := edgeTrack_bounds graph member
  have valid : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  have positive : (1 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  have portZero : PortRow graph 3 := ⟨0,by simp⟩
  have portUp : PortRow graph (3+(drawingGridSize graph : Int)) := ⟨1,by simp⟩
  have portDown : PortRow graph (3+ -(drawingGridSize graph : Int)) := ⟨-1,by simp⟩
  rcases offset_eq_of_span_le_one tagged.1 edgeLocal with offset | offset | offset | offset | offset
  all_goals simp [classifiedCore,offset,CoreJoint,GridSegment.IsHorizontal,GridSegment.IsVertical,Cell.add,Cell.scale,
    portZero,portUp,portDown]
  all_goals try split
  all_goals try simp_all [CoreJoint,GridSegment.IsHorizontal,GridSegment.IsVertical,Cell.add,Cell.scale,
    portZero,portUp,portDown]
  all_goals omega

theorem coreJoint_translated_contains {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {index : Nat} {horizontal : Bool} {endpoint : Cell}
    (joint : CoreJoint graph edge index horizontal endpoint) (cell : Cell) :
    ∃ neighbor ∈ classifiedCore graph edge index,
      (if horizontal then neighbor.segment.IsHorizontal else neighbor.segment.IsVertical) ∧
        (neighbor.segment.translate (Cell.scale (drawingGridSize graph : Int) cell)).RealContains
          (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) cell) endpoint)) := by
  obtain ⟨neighbor,member,axis,start | finish⟩ := joint
  · refine ⟨neighbor,member,axis,?_⟩
    rw [← start]
    exact GridSegment.realContains_start _
  · refine ⟨neighbor,member,axis,?_⟩
    rw [← finish]
    exact GridSegment.realContains_finish _

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
