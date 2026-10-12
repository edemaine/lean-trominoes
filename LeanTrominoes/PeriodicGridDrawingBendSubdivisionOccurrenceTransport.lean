/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionCompatibility
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionRecordLookup
import LeanTrominoes.PeriodicGridDrawingPolygonalSegmentContacts

/-! # Lifted subdivision edges are the corresponding moved polygonal segments -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def subdivisionSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Nat) (edge : PeriodicEdge (Vertex V)) : GridSegment :=
  ⟨position source drawing factor edge.source,
    Cell.add (position source drawing factor edge.target) (Cell.scale (factor*drawing.gridSize) edge.offset)⟩

theorem subdivision_segment_image {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Nat) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing factor).edges.zipIdx) (translate : Cell) (p : ℝ × ℝ) :
    GridPolyline.RealContains ((subdivisionDrawing source drawing factor).realEdgeRoute tagged.2 translate) p ↔
      ((subdivisionSegment source drawing factor tagged.1).translate
        ((subdivisionDrawing source drawing factor).periodTranslation translate)).RealContains p := by
  simp only [realEdgeRoute,subdivision_edgeRoute_of_tagged source drawing factor member,straightRoute,List.map_cons,
    List.map_nil,GridPolyline.RealContains,gridPolylineSegments,List.mem_singleton,exists_eq_left]
  rfl

theorem subdivision_segment_endpoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Nat) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing factor).edges.zipIdx) (translate : Cell) (p : ℝ × ℝ) :
    GridPolyline.RealIsEndpoint ((subdivisionDrawing source drawing factor).realEdgeRoute tagged.2 translate) p ↔
      p=realCell ((subdivisionSegment source drawing factor tagged.1).translate
        ((subdivisionDrawing source drawing factor).periodTranslation translate)).start ∨
      p=realCell ((subdivisionSegment source drawing factor tagged.1).translate
        ((subdivisionDrawing source drawing factor).periodTranslation translate)).finish := by
  simp only [realEdgeRoute,subdivision_edgeRoute_of_tagged source drawing factor member,straightRoute,List.map_cons,
    List.map_nil,GridPolyline.RealIsEndpoint,List.head?_cons,List.getLast?_cons_cons,List.getLast?_singleton,
    Option.some.injEq,subdivisionSegment,GridSegment.translate,exists_eq_left']

theorem lifted_subdivision_segment_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {factor : Nat} (positive : 0 < factor) (edge : PeriodicEdge (Vertex V)) (translate : Cell) :
    (subdivisionSegment source drawing factor edge).translate ((subdivisionDrawing source drawing factor).periodTranslation translate)=
      (absoluteSegment (position source drawing factor) ((factor:Int)*drawing.gridSize) (sourceCell drawing factor) edge).translate
        ((InteriorBends.perturbDrawing drawing factor).periodTranslation (Cell.sub translate (sourceCell drawing factor edge.source))) := by
  unfold subdivisionSegment absoluteSegment GridSegment.translate
  simp only [periodTranslation,subdivisionDrawing_gridSize source drawing positive,
    InteriorBends.perturbDrawing_gridSize drawing positive,Nat.cast_mul]
  congr 1 <;> apply Prod.ext <;> simp only [Cell.add,Cell.sub,Cell.scale] <;> ring

theorem edgeRoute_tagged_mem_of_lt {drawing : PeriodicGridDrawing} {index : Nat} (valid : index < drawing.edgeRoutes.length) :
    (drawing.edgeRoute index,index) ∈ drawing.edgeRoutes.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
  refine ⟨valid,?_⟩
  exact (List.getD_eq_getElem _ _ valid).symm

theorem record_segment_in_moved_route {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {factor : Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing factor) :
    (absoluteSegment (position source drawing factor) ((factor:Int)*drawing.gridSize) (sourceCell drawing factor) record.2,record.1.2) ∈
      (gridPolylineSegments ((InteriorBends.perturbDrawing drawing factor).edgeRoute record.1.1)).zipIdx := by
  obtain ⟨parent,_,indexEq,pieceMember⟩ := record_absolute_segment_member planar member
  rw [← indexEq,InteriorBends.perturbDrawing_edgeRoute]
  exact pieceMember

theorem record_parent_index_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible source) {factor : Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing factor) :
    record.1.1 < (InteriorBends.perturbDrawing drawing factor).edgeRoutes.length := by
  obtain ⟨parent,parentMember,piece,_,rfl⟩ := record_provenance member
  simp only [InteriorBends.perturbDrawing,List.length_map,compatible.2.2.1]
  simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx parentMember

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
