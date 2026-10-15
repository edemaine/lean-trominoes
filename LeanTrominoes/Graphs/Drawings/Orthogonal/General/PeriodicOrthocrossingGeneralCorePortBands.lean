/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreVertical

/-! # A port spine stays between the port row and its edge's private tracks -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def corePortShift {Vertex : Type*} (edge : PeriodicEdge Vertex) : SegmentRole Vertex → Cell
  | .targetPortVertical _ => edge.offset
  | _ => (0,0)

theorem core_port_spine_band {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) (edgeLocal : edge.span ≤ 1) :
    ∀ piece ∈ classifiedCore graph edge index, ∀ port, piece.role.activeVerticalPort = some port →
      piece.segment.start.1 = portX graph port+(drawingGridSize graph : Int)*(corePortShift edge piece.role).1 ∧
        3+(drawingGridSize graph : Int)*(corePortShift edge piece.role).2 ≤
          min piece.segment.start.2 piece.segment.finish.2 ∧
        max piece.segment.start.2 piece.segment.finish.2 ≤
          edgeTrack index+1+(drawingGridSize graph : Int)*(corePortShift edge piece.role).2 := by
  have trackAbove : (3 : Int) < edgeTrack index := by unfold edgeTrack; omega
  rcases offset_eq_of_span_le_one edge edgeLocal with offset | offset | offset | offset | offset
  all_goals simp [classifiedCore,offset,SegmentRole.activeVerticalPort,corePortShift,Cell.add,Cell.scale]
  all_goals try split
  all_goals try simp_all [SegmentRole.activeVerticalPort,corePortShift,Cell.add,Cell.scale]
  all_goals omega

theorem core_port_is_endpoint_port {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    ∀ piece ∈ classifiedCore graph edge index, ∀ port, piece.role.activeVerticalPort = some port →
      (port = sourcePort edge index ∧ corePortShift edge piece.role = (0,0)) ∨
        (port = targetPort edge index ∧ corePortShift edge piece.role = edge.offset) := by
  unfold classifiedCore
  split <;> simp_all [SegmentRole.activeVerticalPort,corePortShift]
  all_goals split <;> simp_all [SegmentRole.activeVerticalPort,corePortShift]

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
