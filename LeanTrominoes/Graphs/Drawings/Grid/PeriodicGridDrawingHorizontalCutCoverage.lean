/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingHorizontalCutTableCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRationalPortOrder
import LeanTrominoes.Common.Geometry.GridSegmentRealUnitColumnSpan

/-! # Horizontal cut coverage and exclusion of virtual rectangle corners -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem horizontal_cut_retained {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (top : Bool) {coordinate : ℚ}
    (nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1)
    (inside : (column : ℚ) < coordinate ∧ coordinate < (column : ℚ)+1)
    (contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains
      ((coordinate : ℝ),((drawing.gridSize : ℚ)*(if top then 1 else 0)-seamPerturbation graph drawing : ℝ))) :
    ∃ key : Nat × Cell, (RectanglePortKey.horizontal top key).Valid graph drawing column ∧
      (RectanglePortKey.horizontal (Vertex := Vertex) top key).parentKey = (tagged.2,cell) ∧
      shiftedSeamAbscissa graph drawing key = coordinate ∧
      (column : ℚ)+columnPerturbation graph drawing < coordinate ∧
      coordinate < (column : ℚ)+1-columnPerturbation graph drawing := by
  have periodBound : (column : ℚ)+1 ≤ drawing.gridSize := by exact_mod_cast (show column+1 ≤ drawing.gridSize by omega)
  have inCell : 0 < coordinate ∧ coordinate < (drawing.gridSize : ℚ) :=
    ⟨lt_of_le_of_lt (by positivity) inside.1,inside.2.trans_le periodBound⟩
  obtain ⟨key,keyMember,index,cellEqual,coordinateEqual⟩ := horizontal_cut_table_coverage planar straight member edgeLocal cell
    (if top then 1 else 0) nonvertical inCell (by cases top <;> simpa using contains)
  have slabEqual : seamAssignedSlab graph drawing key = column := by
    unfold seamAssignedSlab
    rw [← shiftedSeamAbscissa_slab planar straight keyMember,coordinateEqual]
    simp only [rationalSlab,Bool.false_eq_true,false_and,ite_false]
    apply Int.floor_eq_iff.mpr
    simpa only [Int.cast_natCast] using And.intro inside.1.le inside.2
  have margin := shiftedSeamAbscissa_inside_shrunken_slab planar straight (columnPerturbation_positive planar straight)
    (columnPerturbation_le_cutMargin planar straight) keyMember
  rw [slabEqual,coordinateEqual] at margin
  refine ⟨key,⟨keyMember,slabEqual⟩,?_,coordinateEqual,margin⟩
  exact Prod.ext index cellEqual

theorem virtual_column_cut_height_avoids_row_seams {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (right top : Bool)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column) :
    (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
      ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing)) ≠
      (drawing.gridSize : ℚ)*(if top then 1 else 0)-seamPerturbation graph drawing := by
  have epsilonPositive := columnPerturbation_positive planar straight
  have epsilonSmall : columnPerturbation graph drawing < 1 :=
    lt_trans ((columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)) (by norm_num)
  have nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1 := by
    rcases spans with forward | backward <;> omega
  have contains := GridSegment.rational_unit_column_cut_realInteriorContains spans epsilonPositive epsilonSmall right
  intro equal
  have contact : (drawing.liftedStraightSegment tagged.2 cell).RealContains
      ((((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing) : ℚ) : ℝ),
        ((drawing.gridSize : ℚ)*(if top then 1 else 0)-seamPerturbation graph drawing : ℝ)) := by
    have actual := GridSegment.realInteriorContains_implies_realContains contains
    simp only [Int.cast_natCast] at actual
    rw [equal] at actual
    cases top <;> simpa using actual
  have inside : (column : ℚ) < (column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing) ∧
      (column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing) < (column : ℚ)+1 := by
    cases right <;> simp only [Bool.false_eq_true,if_false,if_true] <;> constructor <;> linarith
  obtain ⟨key,_,_,_,lower,upper⟩ := horizontal_cut_retained planar straight member edgeLocal cell column columnBound top nonvertical inside contact
  cases right <;> simp at lower upper <;> linarith

end LeanTrominoes.PeriodicGridDrawing
