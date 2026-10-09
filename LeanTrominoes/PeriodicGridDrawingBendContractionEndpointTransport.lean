/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendContractionEndpoints
import LeanTrominoes.PeriodicGridDrawingBendContractionLiftedPieces

/-! # Endpoint contacts descend to the moved polygonal drawing and ascend to joined routes -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem subdivision_period_scaled {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (copy : Cell) :
    (orthogonalSubdivision source drawing).periodTranslation copy=
      Cell.scale (subdivisionScale drawing)
        ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation copy) := by
  have positive : 0 < bendRefinementFactor drawing := by unfold bendRefinementFactor; omega
  simp only [periodTranslation,orthogonalSubdivision_gridSize,
    InteriorBends.perturbDrawing_gridSize drawing positive,Nat.cast_mul]
  apply Prod.ext <;> simp only [Cell.scale] <;> ring

theorem liftedContractedRoute_endpoints_map {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) (copy : Cell) :
    ((contractedRoute source drawing parent).map (Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy))).head?=
      ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).realEdgeRoute parent.2 copy).head?.map
        (Cell.scale (subdivisionScale drawing)) ∧
    ((contractedRoute source drawing parent).map (Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy))).getLast?=
      ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).realEdgeRoute parent.2 copy).getLast?.map
        (Cell.scale (subdivisionScale drawing)) := by
  have ends := contractedRoute_endpoints_map planar localDrawing localGraph degree member
  have functionEq : Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy) ∘ Cell.scale (subdivisionScale drawing)=
      Cell.scale (subdivisionScale drawing) ∘ Cell.add
        ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation copy) := by
    funext point
    simp only [Function.comp_def,Cell.scale_add,subdivision_period_scaled]
  constructor
  · rw [List.head?_map,ends.1,realEdgeRoute,List.head?_map,Option.map_map,Option.map_map,functionEq]
  · rw [List.getLast?_map,ends.2,realEdgeRoute,List.getLast?_map,Option.map_map,Option.map_map,functionEq]

theorem liftedContractedRoute_endpoint_transport {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) (copy : Cell) {point : Cell}
    (endpoint : GridPolyline.RealIsEndpoint
      ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).realEdgeRoute parent.2 copy) (realCell point)) :
    GridPolyline.RealIsEndpoint ((contractedRoute source drawing parent).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy)))
      (realCell (Cell.scale (subdivisionScale drawing) point)) := by
  have ends := liftedContractedRoute_endpoints_map planar localDrawing localGraph degree member copy
  rcases endpoint with ⟨actual,atHead,equal⟩ | ⟨actual,atLast,equal⟩
  · have same := realCell_injective equal
    subst actual
    exact Or.inl ⟨_,by rw [ends.1,atHead,Option.map_some],rfl⟩
  · have same := realCell_injective equal
    subst actual
    exact Or.inr ⟨_,by rw [ends.2,atLast,Option.map_some],rfl⟩

theorem liftedRefinedPiece_endpoint_preimage {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing (bendRefinementFactor drawing)) (copy : Cell) {p : ℝ × ℝ}
    (endpoint : GridPolyline.RealIsEndpoint (liftedRefinedPiece source drawing record copy) p) :
    ∃ point : Cell, GridPolyline.RealContains
      ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).realEdgeRoute record.1.1 copy)
      (realCell point) ∧ p=realCell (Cell.scale (subdivisionScale drawing) point) := by
  have ends := liftedRefinedPiece_endpoints planar localDrawing localGraph degree member copy
  have pieceMember := record_segment_in_moved_route planar member
  have liftedMember := tagged_segment_translate pieceMember
    ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation copy)
  have routeMember : (absoluteSegment (position source drawing (bendRefinementFactor drawing))
      ((bendRefinementFactor drawing:Int)*drawing.gridSize) (sourceCell drawing (bendRefinementFactor drawing)) record.2).translate
      ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation copy) ∈
      gridPolylineSegments ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).realEdgeRoute record.1.1 copy) :=
    List.fst_mem_of_mem_zipIdx liftedMember
  rcases GridPolyline.realEndpoint_of_prescribed_endpoints ends.1 ends.2 endpoint with atStart | atFinish
  · exact ⟨_,⟨_,routeMember,GridSegment.realContains_start _⟩,atStart⟩
  · exact ⟨_,⟨_,routeMember,GridSegment.realContains_finish _⟩,atFinish⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
