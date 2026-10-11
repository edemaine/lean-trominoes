/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionPieceSimplicity

/-! # Contraction restores the original graph's scaled endpoint positions -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem parentPieces_nonempty {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx) :
    0 < (parentPieces source drawing parent).length := by
  have oldSimple := planar.1.2.1 _ (edgeRoute_mem_of_compatible planar.1.1 parentMember)
  rw [parentPieces_length planar parentMember,gridPolylineSegments_length]
  have long := oldSimple.1
  omega

theorem contractedRoute_endpoints_map {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) :
    (contractedRoute source drawing parent).head?=
      (drawing.edgeRoute parent.2).head?.map
        (Cell.scale (cubicScale drawing)) ∧
    (contractedRoute source drawing parent).getLast?=
      (drawing.edgeRoute parent.2).getLast?.map
        (Cell.scale (cubicScale drawing)) := by
  have positive := parentPieces_nonempty planar localDrawing localGraph parentMember
  have allSimple := fun route member => parentPieces_openSimple planar localDrawing localGraph degree parentMember
    (route := route) member
  obtain ⟨first,firstMember,_,firstRoute,firstPiece⟩ := parentPiece_data planar parentMember positive
  have firstEnds := refinedPiece_endpoints source drawing first
  have oldHead := indexed_gridPolylineSegment_head firstPiece rfl
  have headEq : (contractedRoute source drawing parent).head?=(parentPieces source drawing parent)[0].head? := by
    unfold contractedRoute
    generalize piecesEq : parentPieces source drawing parent=pieces at positive ⊢
    cases pieces with
    | nil => simp only [List.length_nil] at positive; omega
    | cons firstListedRoute rest =>
        have long := (allSimple firstListedRoute (by rw [piecesEq]; simp)).1
        have nonempty : firstListedRoute≠[] := by intro empty; simp only [empty,List.length_nil] at long; omega
        exact GridPolyline.joinRouteChain_head rest nonempty
  constructor
  · rw [headEq,firstRoute,firstEnds.1,oldHead,Option.map_some]
  · let index := (parentPieces source drawing parent).length-1
    have valid : index < (parentPieces source drawing parent).length := by dsimp only [index]; omega
    obtain ⟨last,lastMember,_,lastRoute,lastPiece⟩ := parentPiece_data planar parentMember valid
    have lastEnds := refinedPiece_endpoints source drawing last
    have final : index+1=(gridPolylineSegments
        (drawing.edgeRoute parent.2)).length := by
      rw [← parentPieces_length planar parentMember]
      dsimp only [index]
      omega
    have oldLast := indexed_gridPolylineSegment_last lastPiece final
    rw [contractedRoute,GridPolyline.joinRouteChain_last (fun route member => (allSimple route member).1),
      List.getLast?_eq_getElem?]
    change ((parentPieces source drawing parent)[index]?).bind List.getLast?=_
    rw [List.getElem?_eq_getElem valid,Option.bind_some,lastRoute,lastEnds.2,oldLast,Option.map_some]

theorem contractedRoute_endpoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) :
    (contractedRoute source drawing parent).head?=some (Cell.scale (cubicScale drawing)
      (drawing.vertexPosition source parent.1.source)) ∧
    (contractedRoute source drawing parent).getLast?=some (Cell.add
      (Cell.scale (cubicScale drawing) (drawing.vertexPosition source parent.1.target))
      (Cell.scale (cubicScale drawing*drawing.gridSize) parent.1.offset)) := by
  have endpoints := contractedRoute_endpoints_map planar localDrawing localGraph degree parentMember
  have oldEnds := planar.1.1.2.2.2.2.2 parent parentMember
  rw [oldEnds.1,oldEnds.2] at endpoints
  simp only [Option.map_some] at endpoints
  constructor
  · exact endpoints.1
  · rw [endpoints.2]
    apply congrArg some
    apply Prod.ext <;> simp only [periodTranslation,Cell.scale,Cell.add] <;> ring

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
