/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionPieceSimplicity
import LeanTrominoes.Common.Geometry.GridPolylineRealRouteChainTranslation

/-! # Lifted joined routes retain refined-piece provenance and scaled endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def liftedRefinedPiece {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) (copy : Cell) : List Cell :=
  (refinedPiece source drawing record).map (Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy))

theorem liftedRefinedPiece_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) (copy : Cell) :
    liftedRefinedPiece source drawing record copy=(orthogonalSubdivision source drawing).realEdgeRoute
      (recordIndex source drawing (bendRefinementFactor drawing) record)
      (Cell.add (sourceCell drawing (bendRefinementFactor drawing) record.2.source) copy) := by
  unfold liftedRefinedPiece refinedPiece realEdgeRoute
  rw [List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp only [Function.comp_def,Cell.add,periodTranslation,Cell.scale] <;> ring

theorem liftedRefinedPiece_endpoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing (bendRefinementFactor drawing)) (copy : Cell) :
    (liftedRefinedPiece source drawing record copy).head?=some (Cell.scale (subdivisionScale drawing)
      ((absoluteSegment (position source drawing (bendRefinementFactor drawing))
        ((bendRefinementFactor drawing:Int)*drawing.gridSize) (sourceCell drawing (bendRefinementFactor drawing)) record.2).translate
        ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation copy)).start) ∧
    (liftedRefinedPiece source drawing record copy).getLast?=some (Cell.scale (subdivisionScale drawing)
      ((absoluteSegment (position source drawing (bendRefinementFactor drawing))
        ((bendRefinementFactor drawing:Int)*drawing.gridSize) (sourceCell drawing (bendRefinementFactor drawing)) record.2).translate
        ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation copy)).finish) := by
  have ends := refinedPiece_endpoints planar localDrawing localGraph degree member
  have positive : 0 < bendRefinementFactor drawing := by unfold bendRefinementFactor; omega
  unfold liftedRefinedPiece
  constructor
  · rw [List.head?_map,ends.1]
    simp only [Option.map_some]
    apply congrArg some
    simp only [periodTranslation,orthogonalSubdivision_gridSize,
      InteriorBends.perturbDrawing_gridSize drawing positive,Nat.cast_mul,GridSegment.translate]
    apply Prod.ext <;> simp only [Cell.scale,Cell.add] <;> ring
  · rw [List.getLast?_map,ends.2]
    simp only [Option.map_some]
    apply congrArg some
    simp only [periodTranslation,orthogonalSubdivision_gridSize,
      InteriorBends.perturbDrawing_gridSize drawing positive,Nat.cast_mul,GridSegment.translate]
    apply Prod.ext <;> simp only [Cell.scale,Cell.add] <;> ring

theorem parentRecord_parent {V : Type*} {drawing : PeriodicGridDrawing} {factor : Nat}
    {parent : PeriodicEdge V × Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ parentRecords drawing factor parent) : record.1.1=parent.2 := by
  obtain ⟨piece,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem liftedContractedRoute_contains {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) (copy : Cell) {p : ℝ × ℝ}
    (contains : GridPolyline.RealContains ((contractedRoute source drawing parent).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy))) p) :
    ∃ record ∈ parentRecords drawing (bendRefinementFactor drawing) parent,
      GridPolyline.RealContains (liftedRefinedPiece source drawing record copy) p := by
  obtain ⟨route,member,routeContains⟩ := GridPolyline.joinRouteChain_map_contains
    (parentPieces_chain planar localDrawing localGraph degree parentMember)
    (fun route member => (parentPieces_openSimple planar localDrawing localGraph degree parentMember member).1)
    _ contains
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp member
  exact ⟨record,recordMember,routeContains⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
