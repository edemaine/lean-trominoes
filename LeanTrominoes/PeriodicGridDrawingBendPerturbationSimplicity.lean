/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendPerturbation
import LeanTrominoes.PeriodicGridDrawingPolygonalPointBounds
import LeanTrominoes.GridPolylinePerturbationSimplicity
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision

/-! # Moving polygonal bends inward preserves real simplicity -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem tagged_edge_of_route_mem {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source)
    {route : List Cell} (member : route∈drawing.edgeRoutes) :
    ∃ tagged∈source.edges.zipIdx, drawing.edgeRoute tagged.2=route := by
  let index := drawing.edgeRoutes.idxOf route
  have valid : index<drawing.edgeRoutes.length := List.idxOf_lt_length_of_mem member
  have edgeValid : index<source.edges.length := by rwa [compatible.2.2.1] at valid
  let edge := source.edges[index]
  refine ⟨(edge,index),?_,?_⟩
  · rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨edgeValid,rfl⟩
  · unfold edgeRoute
    rw [List.getD_eq_getElem _ _ valid]
    exact List.getElem_idxOf valid

theorem polygonal_segment_direction_bounds {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {tagged : PeriodicEdge V × Nat} (member : tagged∈source.edges.zipIdx)
    {segment : GridSegment} (segmentMember : segment∈gridPolylineSegments (drawing.edgeRoute tagged.2)) :
    |segment.direction.1|≤2*(drawing.gridSize:Int) ∧ |segment.direction.2|≤2*(drawing.gridSize:Int) := by
  have routeMember := edgeRoute_mem_of_compatible planar.1.1 member
  have long := (planar.1.2.1 _ routeMember).1
  have endpoints := gridPolylineSegments_endpoints_mem segmentMember
  exact local_rectangle_coordinate_difference (localGraph _ (List.fst_mem_of_mem_zipIdx member))
    (polygonal_point_in_local_rectangle localDrawing member long endpoints.1)
    (polygonal_point_in_local_rectangle localDrawing member long endpoints.2)

namespace InteriorBends

theorem perturbDrawing_routesSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8<(factor:Int)) :
    (perturbDrawing drawing factor).RealRoutesAreSimple := by
  intro route member
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨tagged,taggedMember,lookup⟩ := tagged_edge_of_route_mem planar.1.1 oldMember
  have positive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  apply (planar.1.2.1 old oldMember).perturb (factor := (factor:Int)) (bound := 2*(drawing.gridSize:Int)) (by omega) (by omega)
    (point drawing.gridSize factor)
  · intro p _
    exact point_perturbation _ _ _
  · intro segment member
    rw [← lookup] at member
    exact polygonal_segment_direction_bounds planar localDrawing localGraph taggedMember member

end InteriorBends
end LeanTrominoes.PeriodicGridDrawing
