/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreVertical
import LeanTrominoes.Common.Geometry.GridPolylineRealSimpleCertificate
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalTrackSimpleCertificates

/-! # Every private track core is a simple curve -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] core

theorem core_simple_box_certificate {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    GridPolyline.SimpleBoxCertificate (core graph tagged.1 tagged.2) := by
  have sourceBounds := portX_lt_gridSize wellFormed (sourcePort_mem_allPorts graph member)
  have targetBounds := portX_lt_gridSize wellFormed (targetPort_mem_allPorts graph member)
  have sourceBeforeGate := portX_bounds wellFormed (sourcePort_mem_allPorts graph member)
  have targetBeforeGate := portX_bounds wellFormed (targetPort_mem_allPorts graph member)
  have tracks := edgeTrack_bounds graph member
  have indexBound : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  have different := sourcePortX_ne_targetPortX wellFormed member
  have positive : (1 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  rcases offset_eq_of_span_le_one tagged.1 edgeLocal with offset | offset | offset | offset | offset
  · simpa only [core,offset,Cell.add,Cell.scale,mul_zero,add_zero] using
      horizontal_track_simple_certificate _ _ _ different tracks.1
  · by_cases order : portX graph (targetPort tagged.1 tagged.2) < portX graph (sourcePort tagged.1 tagged.2)
    · simp only [core,offset,order,ite_true,Cell.add,Cell.scale,mul_zero,mul_one,add_zero]
      rw [add_comm (drawingGridSize graph : Int) (portX graph (targetPort tagged.1 tagged.2))]
      apply horizontal_track_simple_certificate <;> omega
    · simp only [core,offset,order,ite_false,Cell.add,Cell.scale,mul_zero,mul_one,add_zero]
      rw [add_comm (drawingGridSize graph : Int) (portX graph (targetPort tagged.1 tagged.2))]
      apply boundary_track_simple_certificate <;> omega
  · by_cases order : portX graph (sourcePort tagged.1 tagged.2) < portX graph (targetPort tagged.1 tagged.2)
    · simp only [core,offset,order,ite_true,Cell.add,Cell.scale,mul_zero,mul_neg_one,add_zero]
      convert horizontal_track_simple_certificate (portX graph (sourcePort tagged.1 tagged.2))
        (portX graph (targetPort tagged.1 tagged.2)-(drawingGridSize graph : Int))
        (edgeTrack tagged.2) (by omega) tracks.1 using 1 <;> congr 2 <;> omega
    · simp only [core,offset,order,ite_false,Cell.add,Cell.scale,mul_zero,mul_neg_one,add_zero]
      convert boundary_track_simple_certificate (portX graph (sourcePort tagged.1 tagged.2)) 0
        (portX graph (targetPort tagged.1 tagged.2)-(drawingGridSize graph : Int))
        (edgeTrack tagged.2) (by omega) tracks.1 using 1 <;> congr 2 <;> omega
  · simp only [core,offset,Cell.add,Cell.scale,mul_zero,mul_one,add_zero]
    apply gate_track_simple_certificate <;> omega
  · simp only [core,offset,Cell.add,Cell.scale,mul_zero,mul_neg_one,add_zero]
    apply gate_track_simple_certificate <;> omega

theorem core_isRealSimple {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    GridPolyline.IsRealSimple (core graph tagged.1 tagged.2) :=
  GridPolyline.isRealSimple_of_box_certificate (core_simple_box_certificate wellFormed member edgeLocal)

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
