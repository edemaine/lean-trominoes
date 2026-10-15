/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralContactAssembly

/-! # The general track drawing satisfies the real orthocrossing condition -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core route classifiedCore drawing

theorem core_piece_mem_lifted_route {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2) (cell : Cell) :
    piece.segment.translate (Cell.scale (drawingGridSize graph : Int) cell) ∈
      gridPolylineSegments (translatePolyline (Cell.scale (drawingGridSize graph : Int) cell)
        (route graph orthogonal tagged.1 tagged.2)) := by
  rw [gridPolylineSegments_translatePolyline]
  apply List.mem_map.mpr
  refine ⟨piece.segment,?_,rfl⟩
  rw [route_segments orthogonal degree member]
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_append.mpr
  apply Or.inr
  rw [← classifiedCore_segments]
  exact List.mem_map.mpr ⟨piece,pieceMember,rfl⟩

theorem drawing_realEdgeRoute_of_mem {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (orthogonal : Bool) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (drawing graph orthogonal).realEdgeRoute tagged.2 cell =
      translatePolyline (Cell.scale (drawingGridSize graph : Int) cell) (route graph orthogonal tagged.1 tagged.2) := by
  unfold PeriodicGridDrawing.realEdgeRoute
  rw [drawing_edgeRoute_of_mem graph orthogonal member]
  simp only [PeriodicGridDrawing.periodTranslation,drawing_gridSize,translatePolyline]

theorem drawing_isRealOrthocrossing {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4) (isLocal : graph.IsLocal) :
    (drawing graph orthogonal).IsRealOrthocrossing := by
  intro firstIndex secondIndex firstCell secondCell firstValid secondValid different point firstContains secondContains
  have firstBound : firstIndex < graph.edges.zipIdx.length := by simpa [drawing] using firstValid
  have secondBound : secondIndex < graph.edges.zipIdx.length := by simpa [drawing] using secondValid
  let firstTagged := graph.edges.zipIdx[firstIndex]'firstBound
  let secondTagged := graph.edges.zipIdx[secondIndex]'secondBound
  have firstMember : firstTagged ∈ graph.edges.zipIdx := List.getElem_mem firstBound
  have secondMember : secondTagged ∈ graph.edges.zipIdx := List.getElem_mem secondBound
  have firstId : firstTagged.2 = firstIndex := by simp [firstTagged,List.getElem_zipIdx]
  have secondId : secondTagged.2 = secondIndex := by simp [secondTagged,List.getElem_zipIdx]
  have firstRoute : (drawing graph orthogonal).realEdgeRoute firstIndex firstCell =
      translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell) (route graph orthogonal firstTagged.1 firstTagged.2) := by
    rw [← firstId]
    exact drawing_realEdgeRoute_of_mem graph orthogonal firstMember firstCell
  have secondRoute : (drawing graph orthogonal).realEdgeRoute secondIndex secondCell =
      translatePolyline (Cell.scale (drawingGridSize graph : Int) secondCell) (route graph orthogonal secondTagged.1 secondTagged.2) := by
    rw [← secondId]
    exact drawing_realEdgeRoute_of_mem graph orthogonal secondMember secondCell
  rw [firstRoute] at firstContains
  rw [secondRoute] at secondContains
  have distinctOccurrences : (firstTagged,firstCell) ≠ (secondTagged,secondCell) := by
    intro equal
    apply different
    apply Prod.ext
    · have indices := congrArg (fun taggedCell : (PeriodicEdge Vertex × Nat) × Cell => taggedCell.1.2) equal
      simpa only [firstId,secondId] using indices
    · exact congrArg (fun taggedCell : (PeriodicEdge Vertex × Nat) × Cell => taggedCell.2) equal
  have contact := route_occurrence_contacts wellFormed orthogonal degree firstMember secondMember
    (isLocal firstTagged.1 (List.fst_mem_of_mem_zipIdx firstMember))
    (isLocal secondTagged.1 (List.fst_mem_of_mem_zipIdx secondMember)) distinctOccurrences firstContains secondContains
  rw [firstRoute,secondRoute]
  rcases contact with endpoints | ⟨firstPiece,firstPieceMember,secondPiece,secondPieceMember,crossing⟩
  · exact Or.inl endpoints
  · exact Or.inr ⟨_,core_piece_mem_lifted_route orthogonal degree firstMember firstPieceMember firstCell,
      _,core_piece_mem_lifted_route orthogonal degree secondMember secondPieceMember secondCell,crossing⟩

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
