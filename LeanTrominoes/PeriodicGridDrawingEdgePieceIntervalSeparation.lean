/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceFootprints
import LeanTrominoes.PeriodicGridDrawingFanPieceFootprints

/-! # Distinct pieces of one straight edge have disjoint parameter interiors -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

def cutEdgePiece {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (line : Int) : EdgeRoutePiece :=
  if line = (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 then sourceEdgePiece graph drawing tagged
  else if line = (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 then targetEdgePiece graph drawing tagged
  else crossingEdgePiece graph drawing tagged.2 line

theorem nonverticalEdgePieces_open_location {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {piece : EdgeRoutePiece} (member : piece ∈ nonverticalEdgePieces graph drawing tagged)
    (parameter : ℚ) (after : piece.start < parameter) (before : parameter < piece.finish) :
    (∃ line : Int, CutContains (columnPerturbation graph drawing) line
        ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter parameter).1 ∧
      piece = cutEdgePiece graph drawing tagged line) ∨
      ∃ column : Nat, column < drawing.gridSize ∧ ∃ cell : Cell,
        rectangleEdgePiece? graph drawing tagged.2 column cell = some piece ∧
        SlabInteriorContains (columnPerturbation graph drawing) ((column : Int)+(drawing.gridSize : Int)*cell.1)
          ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter parameter).1 ∧
        RowInteriorContains (drawing.gridSize : ℚ) (seamPerturbation graph drawing) cell.2
          ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter parameter).2 := by
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((source | rectangle) | crossing) | target
  · subst piece
    exact Or.inl ⟨_,sourceEdgePiece_open_footprint planar straight tagged nonvertical parameter after before,by simp [cutEdgePiece]⟩
  · obtain ⟨column,columnMember,rectangleMember⟩ := List.mem_flatMap.mp rectangle
    obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp rectangleMember
    have columnBound := List.mem_range.mp columnMember
    exact Or.inr ⟨column,columnBound,cell,lookup,
      rectangleEdgePiece?_open_footprint planar graphLocal straight tagged.2 column columnBound cell lookup parameter after before⟩
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have equal := Option.some.inj lookup
    subst piece
    have sourceDifferent : line ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 := by rcases crosses with forward | backward <;> omega
    have targetDifferent : line ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
    exact Or.inl ⟨line,crossingEdgePiece_open_footprint planar straight tagged.2 line crosses parameter after before,
      by simp [cutEdgePiece,sourceDifferent,targetDifferent]⟩
  · subst piece
    exact Or.inl ⟨_,targetEdgePiece_open_footprint planar straight tagged nonvertical parameter after before,
      by simp [cutEdgePiece,nonvertical.symm]⟩

theorem rectangle_piece_index_eq {drawing : PeriodicGridDrawing} {firstColumn lastColumn : Nat}
    (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    {firstCell lastCell : Cell}
    (columnEqual : (firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1 =
      (lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1)
    (rowEqual : firstCell.2 = lastCell.2) : firstColumn = lastColumn ∧ firstCell = lastCell := by
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstIntBound : (firstColumn : Int) < drawing.gridSize := by exact_mod_cast firstBound
  have lastIntBound : (lastColumn : Int) < drawing.gridSize := by exact_mod_cast lastBound
  have residues := congrArg (fun coordinate : Int => coordinate % (drawing.gridSize : Int)) columnEqual
  simp only [Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by omega : (0 : Int) ≤ firstColumn) firstIntBound,
    Int.emod_eq_of_lt (by omega : (0 : Int) ≤ lastColumn) lastIntBound] at residues
  have columns : firstColumn = lastColumn := by exact_mod_cast residues
  refine ⟨columns,Prod.ext ?_ rowEqual⟩
  apply mul_left_cancel₀ positive.ne'
  rw [columns] at columnEqual
  omega

def EdgeRoutePiece.InteriorsDisjoint (first last : EdgeRoutePiece) : Prop :=
  ∀ parameter : ℚ, first.start < parameter → parameter < first.finish →
    last.start < parameter → parameter < last.finish → False

theorem nonverticalEdgePieces_interiors_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {first last : EdgeRoutePiece} (firstMember : first ∈ nonverticalEdgePieces graph drawing tagged)
    (lastMember : last ∈ nonverticalEdgePieces graph drawing tagged) (different : first ≠ last) : first.InteriorsDisjoint last := by
  intro parameter firstAfter firstBefore lastAfter lastBefore
  have firstLocation := nonverticalEdgePieces_open_location planar graphLocal straight tagged nonvertical firstMember parameter firstAfter firstBefore
  have lastLocation := nonverticalEdgePieces_open_location planar graphLocal straight tagged nonvertical lastMember parameter lastAfter lastBefore
  have epsilonPositive := columnPerturbation_positive planar straight
  have epsilonSmall := (columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)
  rcases firstLocation with ⟨firstLine,firstCut,firstEqual⟩ | ⟨firstColumn,firstBound,firstCell,firstLookup,firstSlab,firstRow⟩
  · rcases lastLocation with ⟨lastLine,lastCut,lastEqual⟩ | ⟨lastColumn,lastBound,lastCell,lastLookup,lastSlab,lastRow⟩
    · have lines := cut_line_unique epsilonSmall firstCut lastCut
      exact different (firstEqual.trans (by simpa only [lines] using lastEqual.symm))
    · exact cut_slab_disjoint firstCut lastSlab
  · rcases lastLocation with ⟨lastLine,lastCut,lastEqual⟩ | ⟨lastColumn,lastBound,lastCell,lastLookup,lastSlab,lastRow⟩
    · exact cut_slab_disjoint lastCut firstSlab
    · have columns := slab_column_unique epsilonPositive.le firstSlab lastSlab
      have positive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
      have rows := row_unique positive firstRow lastRow
      have indices := rectangle_piece_index_eq firstBound lastBound columns rows
      rw [indices.1,indices.2] at firstLookup
      exact different (Option.some.inj (firstLookup.symm.trans lastLookup))

end LeanTrominoes.PeriodicGridDrawing
