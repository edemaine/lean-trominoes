/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionEndpoints
import LeanTrominoes.PeriodicGridDrawingRawBendContractionLiftedPieces

/-! # Endpoint contacts descend to the original drawing and ascend to cubic joined routes -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem liftedContractedRoute_endpoints_map {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) (copy : Cell) :
    ((contractedRoute source drawing parent).map (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy))).head?=
      (drawing.realEdgeRoute parent.2 copy).head?.map (Cell.scale (cubicScale drawing)) ∧
    ((contractedRoute source drawing parent).map (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy))).getLast?=
      (drawing.realEdgeRoute parent.2 copy).getLast?.map (Cell.scale (cubicScale drawing)) := by
  have ends := contractedRoute_endpoints_map planar localDrawing localGraph degree member
  have functionEq : Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy) ∘ Cell.scale (cubicScale drawing)=
      Cell.scale (cubicScale drawing) ∘ Cell.add (drawing.periodTranslation copy) := by
    funext point
    apply Prod.ext <;> simp only [Function.comp_def,periodTranslation,Cell.scale,Cell.add] <;> ring
  constructor
  · rw [List.head?_map,ends.1,realEdgeRoute,List.head?_map,Option.map_map,Option.map_map,functionEq]
  · rw [List.getLast?_map,ends.2,realEdgeRoute,List.getLast?_map,Option.map_map,Option.map_map,functionEq]

theorem liftedContractedRoute_endpoint_transport {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) (copy : Cell) {point : Cell}
    (endpoint : GridPolyline.RealIsEndpoint (drawing.realEdgeRoute parent.2 copy) (realCell point)) :
    GridPolyline.RealIsEndpoint ((contractedRoute source drawing parent).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy))) (realCell (Cell.scale (cubicScale drawing) point)) := by
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
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record ∈ records source drawing)
    (copy : Cell) {p : ℝ × ℝ} (endpoint : GridPolyline.RealIsEndpoint (liftedRefinedPiece source drawing record copy) p) :
    ∃ point : Cell, GridPolyline.RealContains (drawing.realEdgeRoute record.1.1 copy) (realCell point) ∧
      p=realCell (Cell.scale (cubicScale drawing) point) := by
  have ends := liftedRefinedPiece_endpoints source drawing record copy
  have pieceMember := record_segment_in_original_route planar.1 member
  have liftedMember := tagged_segment_translate pieceMember (drawing.periodTranslation copy)
  have routeMember : (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).translate
      (drawing.periodTranslation copy) ∈ gridPolylineSegments (drawing.realEdgeRoute record.1.1 copy) :=
    List.fst_mem_of_mem_zipIdx liftedMember
  rcases GridPolyline.realEndpoint_of_prescribed_endpoints ends.1 ends.2 endpoint with atStart | atFinish
  · exact ⟨_,⟨_,routeMember,GridSegment.realContains_start _⟩,atStart⟩
  · exact ⟨_,⟨_,routeMember,GridSegment.realContains_finish _⟩,atFinish⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
