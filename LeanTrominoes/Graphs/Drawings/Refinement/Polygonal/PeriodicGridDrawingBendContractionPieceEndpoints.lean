/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionRecords
import LeanTrominoes.Common.Geometry.GridPolylineRealReplacementContacts

/-! # Refined subedges retain the scaled endpoints of their polygonal pieces -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem orthogonalSubdivision_vertexPosition {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {vertex : Vertex V}
    (member : vertex ∈ (subdivisionGraph source drawing (bendRefinementFactor drawing)).vertices) :
    (orthogonalSubdivision source drawing).vertexPosition
      (subdivisionGraph source drawing (bendRefinementFactor drawing)) vertex=
    Cell.scale (subdivisionScale drawing) (position source drawing (bendRefinementFactor drawing) vertex) := by
  have positive : 0 < bendRefinementFactor drawing := by unfold bendRefinementFactor; omega
  rw [orthogonalSubdivision,straightRefinementDrawing_vertexPosition,
    subdivision_vertexPosition_eq source drawing _ member,subdivisionDrawing_gridSize source drawing positive]
  rfl

theorem refinedPiece_endpoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing (bendRefinementFactor drawing)) :
    (refinedPiece source drawing record).head?=some (Cell.scale (subdivisionScale drawing)
      (absoluteSegment (position source drawing (bendRefinementFactor drawing))
        ((bendRefinementFactor drawing:Int)*drawing.gridSize) (sourceCell drawing (bendRefinementFactor drawing)) record.2).start) ∧
    (refinedPiece source drawing record).getLast?=some (Cell.scale (subdivisionScale drawing)
      (absoluteSegment (position source drawing (bendRefinementFactor drawing))
        ((bendRefinementFactor drawing:Int)*drawing.gridSize) (sourceCell drawing (bendRefinementFactor drawing)) record.2).finish) := by
  have outputPlanar := orthogonalSubdivision_planar planar localDrawing localGraph degree
  have taggedMember := recordIndex_tagged member
  have endpoints := outputPlanar.1.1.2.2.2.2.2 _ taggedMember
  have vertices := outputPlanar.1.1.1.2 record.2 (List.fst_mem_of_mem_zipIdx taggedMember)
  unfold refinedPiece realEdgeRoute
  constructor
  · rw [List.head?_map,endpoints.1]
    simp only [Option.map_some,orthogonalSubdivision_vertexPosition vertices.1]
    apply congrArg some
    simp only [periodTranslation,orthogonalSubdivision_gridSize,Nat.cast_mul,absoluteSegment]
    apply Prod.ext <;> simp only [Cell.add,Cell.scale] <;> ring
  · rw [List.getLast?_map,endpoints.2]
    simp only [Option.map_some,orthogonalSubdivision_vertexPosition vertices.2]
    apply congrArg some
    simp only [periodTranslation,orthogonalSubdivision_gridSize,Nat.cast_mul,absoluteSegment]
    apply Prod.ext <;> simp only [Cell.add,Cell.scale] <;> ring

theorem refinedPiece_endpoint_contacts {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {first second : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (firstMember : first ∈ records source drawing (bendRefinementFactor drawing))
    (secondMember : second ∈ records source drawing (bendRefinementFactor drawing))
    (different : first.1≠second.1) {p : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (refinedPiece source drawing first) p)
    (secondContains : GridPolyline.RealContains (refinedPiece source drawing second) p) :
    GridPolyline.RealIsEndpoint (refinedPiece source drawing first) p ∧
      GridPolyline.RealIsEndpoint (refinedPiece source drawing second) p := by
  have outputPlanar := orthogonalSubdivision_planar planar localDrawing localGraph degree
  have firstValid : recordIndex source drawing (bendRefinementFactor drawing) first <
      (orthogonalSubdivision source drawing).edgeRoutes.length := by
    simpa only [orthogonalSubdivision,straightRefinementDrawing,List.length_map,List.length_zipIdx] using recordIndex_valid firstMember
  have secondValid : recordIndex source drawing (bendRefinementFactor drawing) second <
      (orthogonalSubdivision source drawing).edgeRoutes.length := by
    simpa only [orthogonalSubdivision,straightRefinementDrawing,List.length_map,List.length_zipIdx] using recordIndex_valid secondMember
  apply outputPlanar.2 _ _ _ _ firstValid secondValid ?_ p firstContains secondContains
  intro equal
  have indexEq : recordIndex source drawing (bendRefinementFactor drawing) first=
      recordIndex source drawing (bendRefinementFactor drawing) second := congrArg Prod.fst equal
  have firstAt := recordAt_recordIndex firstMember
  have secondAt := recordAt_recordIndex secondMember
  rw [indexEq,secondAt] at firstAt
  exact different (congrArg Prod.fst firstAt.symm)

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
