/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendPerturbationContacts

/-! # Moving bends inward preserves avoidance of graph vertices -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

private theorem constant_contains_eq (cell : Cell) {p : ℝ × ℝ}
    (contains : (GridSegment.mk cell cell).RealContains p) : p=realCell cell := by
  obtain ⟨t,_,_,x,y⟩ := contains
  exact Prod.ext (by simpa [realCell] using x) (by simpa [realCell] using y)

theorem perturbDrawing_verticesAvoidRoutes {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8<(factor:Int)) :
    (perturbDrawing drawing factor).RealVerticesAvoidRoutes := by
  intro moved movedMember vertexCell edgeCell index valid contains
  obtain ⟨vertex,vertexMember,rfl⟩ := List.mem_map.mp movedMember
  have gridPositive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0<factor := by omega
  have oldValid : index<drawing.edgeRoutes.length := by simpa only [perturbDrawing,List.length_map] using valid
  let oldPoint := Cell.add vertex (drawing.periodTranslation vertexCell)
  let newPoint := Cell.scale factor oldPoint
  have newEqual : Cell.add (Cell.scale factor vertex) ((perturbDrawing drawing factor).periodTranslation vertexCell)=newPoint := by
    apply Prod.ext <;> simp only [periodTranslation,perturbDrawing_gridSize drawing positive,Nat.cast_mul,Cell.add,Cell.scale,
      oldPoint,newPoint] <;> ring
  rw [newEqual] at contains ⊢
  by_cases oldContains : GridPolyline.RealContains (drawing.realEdgeRoute index edgeCell) (realCell oldPoint)
  · have oldEndpoint := planar.1.2.2 vertex vertexMember vertexCell edgeCell index oldValid oldContains
    let base := Cell.sub oldPoint (drawing.periodTranslation edgeCell)
    have reconstruct : Cell.add (drawing.periodTranslation edgeCell) base=oldPoint := by
      apply Prod.ext <;> simp only [base,Cell.add,Cell.sub] <;> omega
    have endpointAtBase : GridPolyline.RealIsEndpoint (drawing.realEdgeRoute index edgeCell)
        (realCell (Cell.add (drawing.periodTranslation edgeCell) base)) := by rwa [reconstruct]
    have movedEndpoint := lifted_endpoint_transport positive endpointAtBase
    have bounds := planar.1.1.2.2.2.2.1 vertex vertexMember
    have movedEqual : liftedPoint drawing factor edgeCell base=newPoint := by
      rw [liftedPoint_at_vertex bounds edgeCell vertexCell reconstruct]
      apply Prod.ext <;> simp only [oldPoint,newPoint,periodTranslation,Cell.add,Cell.scale] <;> ring
    rwa [movedEqual] at movedEndpoint
  · obtain ⟨segment,segmentMember,segmentContains⟩ := moved_segment_provenance positive contains
    have directions := polygonal_direction_bounds_of_index planar localDrawing localGraph oldValid segmentMember
    have disjoint : ∀ p : ℝ × ℝ, (GridSegment.mk oldPoint oldPoint).RealContains p →
        ¬(segment.translate (drawing.periodTranslation edgeCell)).RealContains p := by
      intro p pointContains segmentContains
      have same := constant_contains_eq oldPoint pointContains
      rw [same] at segmentContains
      exact oldContains (lifted_segment_in_route segmentMember segmentContains)
    have pointPerturbed : GridSegment.EndpointPerturbation factor (GridSegment.mk oldPoint oldPoint)
        (GridSegment.mk newPoint newPoint) := by
      have pointBound : GridSegment.PointPerturbation factor oldPoint newPoint := by
        simp only [GridSegment.PointPerturbation,newPoint,Cell.scale,sub_self,abs_zero]
        exact ⟨by norm_num,by norm_num⟩
      exact ⟨pointBound,pointBound⟩
    have separated := GridSegment.perturbations_disjoint (factor := (factor:Int)) (bound := 2*(drawing.gridSize:Int))
      (by omega) (by omega)
      (by simp only [GridSegment.direction,sub_self,abs_zero]; constructor <;> omega)
      (by simpa only [GridSegment.direction_translate] using directions) disjoint pointPerturbed
      (moved_lifted_segment_perturbed drawing factor segment edgeCell) (realCell newPoint)
      (GridSegment.realContains_start _) segmentContains
    exact separated.elim

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
