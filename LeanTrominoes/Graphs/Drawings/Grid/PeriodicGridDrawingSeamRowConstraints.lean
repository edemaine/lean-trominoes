/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCrossingEnumeration
import LeanTrominoes.Graphs.Drawings.Grid.FiniteRationalSlabPerturbation

/-! # Additional affine constraints keep column crossings in their original rows -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalPerturbation

def seamRowConstraintValues {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : List (ℚ × ℚ) :=
  (List.range drawing.gridSize).flatMap fun (column : Nat) =>
    (verticalCrossingCopies graph drawing (column : Int)).flatMap fun key =>
      [(0,0),((drawing.gridSize : ℚ)-(drawing.liftedStraightSegment key.1 key.2).rationalLineHeight (column : Int),1)]

theorem seamRowConstraintValues_members {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (member : key ∈ verticalCrossingCopies graph drawing column) :
    (0,0) ∈ seamRowConstraintValues graph drawing ∧
      ((drawing.gridSize : ℚ)-(drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column,1) ∈ seamRowConstraintValues graph drawing := by
  constructor
  · exact List.mem_flatMap.mpr ⟨column,List.mem_range.mpr columnBound,List.mem_flatMap.mpr ⟨key,member,by simp⟩⟩
  · exact List.mem_flatMap.mpr ⟨column,List.mem_range.mpr columnBound,List.mem_flatMap.mpr ⟨key,member,by simp⟩⟩

theorem pairBound_row_gap {grid : Nat} {height : ℚ} (upper : height < grid) :
    pairBound (0,0) ((grid : ℚ)-height,1) = ((grid : ℚ)-height)/2 := by
  norm_num [pairBound,sub_pos.mpr upper]

end LeanTrominoes.PeriodicGridDrawing
