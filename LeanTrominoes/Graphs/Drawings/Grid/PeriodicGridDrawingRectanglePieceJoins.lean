/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRowPortJoins
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceBoundaryPorts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceIntervalSeparation

/-! # Consecutive computed rectangle pieces join at their common row-seam port -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

theorem rectangle_distinct_ports_join_of_original_point {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) {first last : RectanglePortKey Vertex}
    (firstValid : first.Valid graph drawing firstColumn) (lastValid : last.Valid graph drawing lastColumn)
    (firstParent : first.parentKey = (index,Cell.scale (-1) firstCell))
    (lastParent : last.parentKey = (index,Cell.scale (-1) lastCell))
    (oldPointEqual : rectanglePortOriginalPoint graph drawing firstColumn firstCell first =
      rectanglePortOriginalPoint graph drawing lastColumn lastCell last)
    (different : (firstColumn,firstCell) ≠ (lastColumn,lastCell)) :
    rectangleLiftedPortPoint graph drawing firstColumn firstCell first =
      rectangleLiftedPortPoint graph drawing lastColumn lastCell last := by
  have firstBounds := rectanglePortOriginalPoint_bounds planar graphLocal straight firstColumn firstCell firstValid
  have lastBounds := rectanglePortOriginalPoint_bounds planar graphLocal straight lastColumn lastCell lastValid
  rw [← oldPointEqual] at lastBounds
  have columns := closed_slab_column_unique (columnPerturbation_positive planar straight) firstBounds.1 lastBounds.1
  have indices := rectangle_piece_index_eq firstBound lastBound
    (firstCell := (firstCell.1,0)) (lastCell := (lastCell.1,0)) columns rfl
  have projected := congrArg (fun cell : Cell => cell.1) indices.2
  have cellX : firstCell.1 = lastCell.1 := projected
  have columnEqual := indices.1
  subst lastColumn
  have positive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  rcases closed_row_contact_cases positive firstBounds.2 lastBounds.2 with sameRow | ⟨adjacent,_⟩ | ⟨adjacent,_⟩
  · exact (different (Prod.ext rfl (Prod.ext cellX sameRow))).elim
  · have cellsEqual : lastCell = Cell.add firstCell (0,1) := by
      apply Prod.ext
      · simpa only [Cell.add,add_zero] using cellX.symm
      · exact adjacent
    rw [cellsEqual] at lastParent oldPointEqual ⊢
    exact rectangle_ports_join_across_row planar graphLocal straight index firstColumn firstCell firstValid lastValid firstParent lastParent oldPointEqual
  · have cellsEqual : firstCell = Cell.add lastCell (0,1) := by
      apply Prod.ext
      · simpa only [Cell.add,add_zero] using cellX
      · exact adjacent
    rw [cellsEqual] at firstParent oldPointEqual ⊢
    exact (rectangle_ports_join_across_row planar graphLocal straight index firstColumn lastCell lastValid firstValid lastParent firstParent oldPointEqual.symm).symm

theorem rectangleEdgePiece?_join {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) {firstPiece lastPiece : EdgeRoutePiece}
    (firstLookup : rectangleEdgePiece? graph drawing index firstColumn firstCell = some firstPiece)
    (lastLookup : rectangleEdgePiece? graph drawing index lastColumn lastCell = some lastPiece)
    (boundary : firstPiece.finish = lastPiece.start) : firstPiece.route.getLast? = lastPiece.route.head? := by
  have firstPositive := (rectangleEdgePiece?_valid planar degree graphLocal straight index firstColumn firstCell firstLookup).2.1
  have different : (firstColumn,firstCell) ≠ (lastColumn,lastCell) := by
    intro equal
    have columns := congrArg Prod.fst equal
    have cells := congrArg Prod.snd equal
    change firstColumn = lastColumn at columns
    change firstCell = lastCell at cells
    rw [columns,cells] at firstLookup
    have pieces := Option.some.inj (firstLookup.symm.trans lastLookup)
    have starts := congrArg EdgeRoutePiece.start pieces
    linarith
  cases firstChord : rectangleParentChord graph drawing firstColumn (index,Cell.scale (-1) firstCell) with
  | none => simp [rectangleEdgePiece?,firstChord] at firstLookup
  | some firstKeys =>
    cases lastChord : rectangleParentChord graph drawing lastColumn (index,Cell.scale (-1) lastCell) with
    | none => simp [rectangleEdgePiece?,lastChord] at lastLookup
    | some lastKeys =>
      let firstKey := if rectangleParentForward graph drawing firstColumn (index,Cell.scale (-1) firstCell) firstKeys.1 firstKeys.2 then firstKeys.2 else firstKeys.1
      let lastKey := if rectangleParentForward graph drawing lastColumn (index,Cell.scale (-1) lastCell) lastKeys.1 lastKeys.2 then lastKeys.1 else lastKeys.2
      have firstData := rectangleParentChord_data graph drawing firstColumn (index,Cell.scale (-1) firstCell) firstChord
      have lastData := rectangleParentChord_data graph drawing lastColumn (index,Cell.scale (-1) lastCell) lastChord
      have firstValidParent : firstKey.Valid graph drawing firstColumn ∧ firstKey.parentKey = (index,Cell.scale (-1) firstCell) := by
        dsimp only [firstKey]
        split_ifs
        · exact ⟨firstData.2.1,firstData.2.2.2.1⟩
        · exact ⟨firstData.1,firstData.2.2.1⟩
      have lastValidParent : lastKey.Valid graph drawing lastColumn ∧ lastKey.parentKey = (index,Cell.scale (-1) lastCell) := by
        dsimp only [lastKey]
        split_ifs
        · exact ⟨lastData.1,lastData.2.2.1⟩
        · exact ⟨lastData.2.1,lastData.2.2.2.1⟩
      have firstOld := rectangleEdgePiece?_endpoint_original_points planar graphLocal straight index firstColumn firstCell firstLookup firstChord
      have lastOld := rectangleEdgePiece?_endpoint_original_points planar graphLocal straight index lastColumn lastCell lastLookup lastChord
      have oldPointEqual : rectanglePortOriginalPoint graph drawing firstColumn firstCell firstKey =
          rectanglePortOriginalPoint graph drawing lastColumn lastCell lastKey :=
        firstOld.2.symm.trans ((congrArg (fun parameter => (drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter parameter) boundary).trans lastOld.1)
      have pointsEqual := rectangle_distinct_ports_join_of_original_point planar graphLocal straight index firstColumn lastColumn firstBound lastBound
        firstCell lastCell firstValidParent.1 lastValidParent.1 firstValidParent.2 lastValidParent.2 oldPointEqual different
      have firstPorts := rectangleEdgePiece?_boundary_ports index firstColumn firstCell firstLookup firstChord
      have lastPorts := rectangleEdgePiece?_boundary_ports index lastColumn lastCell lastLookup lastChord
      exact firstPorts.2.1.trans ((congrArg some pointsEqual).trans lastPorts.1.symm)

theorem rectangleEdgePieces_join {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) {first last : EdgeRoutePiece}
    (firstMember : first ∈ rectangleEdgePieces graph drawing index) (lastMember : last ∈ rectangleEdgePieces graph drawing index)
    (boundary : first.finish = last.start) : first.route.getLast? = last.route.head? := by
  obtain ⟨firstColumn,firstColumnMember,firstPieceMember⟩ := List.mem_flatMap.mp firstMember
  obtain ⟨firstCell,_,firstLookup⟩ := List.mem_filterMap.mp firstPieceMember
  obtain ⟨lastColumn,lastColumnMember,lastPieceMember⟩ := List.mem_flatMap.mp lastMember
  obtain ⟨lastCell,_,lastLookup⟩ := List.mem_filterMap.mp lastPieceMember
  exact rectangleEdgePiece?_join planar degree graphLocal straight index firstColumn lastColumn
    (List.mem_range.mp firstColumnMember) (List.mem_range.mp lastColumnMember) firstCell lastCell firstLookup lastLookup boundary

end LeanTrominoes.PeriodicGridDrawing
