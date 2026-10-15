/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationFanOccurrences

/-! # A fan can meet only the trimmed core of its own edge occurrence -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem trimmedCore_endpoint_midpoint (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) {point : ℝ × ℝ}
    (endpoint : GridPolyline.RealIsEndpoint (trimmedCore drawing tagged.2 cell) point) :
    ∃ target : Bool, point = realCell
      (Cell.add (Cell.scale 32 (liftedVertex graph drawing (endpointPort tagged target).vertex (portCell tagged cell target)))
        (Cell.scale 8 (portSide drawing (endpointPort tagged target)).direction.step)) := by
  rcases endpoint with ⟨actual,head,pointEq⟩ | ⟨actual,last,pointEq⟩
  · have fanLast := fanAt_last distinct chosen (sourcePort_mem_allPorts graph member)
      (liftedVertex graph drawing tagged.1.source cell)
    have middleHead := (sourceFan_joint valid orthogonal distinct chosen member cell).symm.trans fanLast
    have equal := Option.some.inj (head.symm.trans middleHead)
    refine ⟨false,?_⟩
    simpa [endpointPort,portCell,sourcePort,equal] using pointEq
  · have fanLast := fanAt_last distinct chosen (targetPort_mem_allPorts graph member)
      (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset))
    have middleLast := targetFan_joint valid orthogonal distinct chosen member cell
    rw [List.head?_reverse] at middleLast
    have equal := Option.some.inj (last.symm.trans (middleLast.trans fanLast))
    refine ⟨true,?_⟩
    simpa [endpointPort,portCell,targetPort,equal] using pointEq

theorem fan_core_occurrence_contact (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aTarget : Bool) (aCell bCell : Cell) {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (fanAt graph drawing chosen (endpointPort a aTarget)
        (liftedVertex graph drawing (endpointPort a aTarget).vertex (portCell a aCell aTarget))) point)
    (coreContains : GridPolyline.RealContains (trimmedCore drawing b.2 bCell) point) :
    (a.2,aCell) = (b.2,bCell) := by
  have fm := endpointPort_mem graph am aTarget
  have contact := fanAt_trimmedRoute_contact distinct chosen fm (liftedRoute_simple valid bm bCell)
    (liftedRoute_orthogonal valid.1 orthogonal bm bCell) _
    (liftedRoute_vertexAvoidance valid bm (port_vertex_mem valid.1.1 fm) _ _) fanContains coreContains
  obtain ⟨bTarget,bMidpoint⟩ := trimmedCore_endpoint_midpoint valid orthogonal distinct chosen bm bCell contact.2
  have ports := fan_midpoint_identifies_port valid.1 distinct chosen fm (endpointPort_mem graph bm bTarget)
    fanContains contact.1 bMidpoint
  exact endpoint_occurrence_injective am bm ports.1 ports.2

theorem trimmed_cores_disjoint (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aCell bCell : Cell) (different : (a.2,aCell) ≠ (b.2,bCell)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (trimmedCore drawing a.2 aCell) point) :
    ¬ GridPolyline.RealContains (trimmedCore drawing b.2 bCell) point := by
  intro secondContains
  have ao := liftedRoute_orthogonal planar.1.1 orthogonal am aCell
  have bo := liftedRoute_orthogonal planar.1.1 orthogonal bm bCell
  have firstOld := (GridPolyline.realContains_scale_inverse _ (by norm_num : (32 : Int) ≠ 0) _).mp
    (GridPolyline.clippedScaledRoute_realContains_source ao firstContains)
  have secondOld := (GridPolyline.realContains_scale_inverse _ (by norm_num : (32 : Int) ≠ 0) _).mp
    (GridPolyline.clippedScaledRoute_realContains_source bo secondContains)
  have firstValid : a.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]; exact List.snd_lt_of_mem_zipIdx am
  have secondValid : b.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]; exact List.snd_lt_of_mem_zipIdx bm
  have contact := (planar.2 a.2 b.2 aCell bCell firstValid secondValid different _ firstOld secondOld).1
  rcases contact with ⟨anchor,head,equal⟩ | ⟨anchor,last,equal⟩
  · have actual := GridPolyline.realPoint_eq_scaledCell_of_div_eq (by norm_num : (32 : Int) ≠ 0) equal
    apply GridPolyline.clippedScaledRoute_not_contains_scaled_endpoint (liftedRoute_simple planar.1 am aCell) ao
      (Or.inl ⟨anchor,head,rfl⟩)
    simpa only [actual,trimmedCore] using firstContains
  · have actual := GridPolyline.realPoint_eq_scaledCell_of_div_eq (by norm_num : (32 : Int) ≠ 0) equal
    apply GridPolyline.clippedScaledRoute_not_contains_scaled_endpoint (liftedRoute_simple planar.1 am aCell) ao
      (Or.inr ⟨anchor,last,rfl⟩)
    simpa only [actual,trimmedCore] using firstContains

end LeanTrominoes.GeneralVertexNormalization
