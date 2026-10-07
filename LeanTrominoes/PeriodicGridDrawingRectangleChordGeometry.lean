/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePortParents
import LeanTrominoes.RealRectangleBoundaryUniqueSides
import LeanTrominoes.PeriodicGridDrawingStraightInteriorsDisjoint

/-! # Rectangle chord ports are unique on each side and separated by parent edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem integer_ne_perturbed_cut (line coordinate : Int) {epsilon : ℚ}
    (positive : 0 < epsilon) (small : epsilon < 1) (negative : Bool) :
    (coordinate : ℝ) ≠ (line : ℝ)+(if negative then -(epsilon : ℝ) else (epsilon : ℝ)) := by
  have positiveReal : (0 : ℝ) < epsilon := by exact_mod_cast positive
  have smallReal : (epsilon : ℝ) < 1 := by exact_mod_cast small
  cases negative
  · intro equal
    have lowerReal : (line : ℝ) < coordinate := by simp only [Bool.false_eq_true,ite_false] at equal; linarith
    have upperReal : (coordinate : ℝ) < (line : ℝ)+1 := by simp only [Bool.false_eq_true,ite_false] at equal; linarith
    have lower : line < coordinate := by exact_mod_cast lowerReal
    have upper : coordinate < line+1 := by exact_mod_cast upperReal
    omega
  · intro equal
    have lowerReal : (line : ℝ)-1 < coordinate := by simp only [ite_true] at equal; linarith
    have upperReal : (coordinate : ℝ) < line := by simp only [ite_true] at equal; linarith
    have lower : line-1 < coordinate := by exact_mod_cast lowerReal
    have upper : coordinate < line := by exact_mod_cast upperReal
    omega

theorem virtualSlab_ports_eq_of_same_side {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {segment : GridSegment} {first last : RealRectangleBoundary.Port}
    (sameSide : first.side = last.side)
    (firstContains : segment.RealContains (first.shiftedPoint
      (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ)))
    (lastContains : segment.RealContains (last.shiftedPoint
      (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ))) : first = last := by
  have epsilonPositive := columnPerturbation_positive planar straight
  have epsilonSmall : columnPerturbation graph drawing < 1 :=
    lt_trans ((columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)) (by norm_num)
  have originEqual : virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0 =
      ((column : ℝ)+(columnPerturbation graph drawing : ℝ),-(seamPerturbation graph drawing : ℝ)) := by
    apply Prod.ext <;> simp [virtualSlabOrigin]
  have widthEqual : ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) = 1-2*(columnPerturbation graph drawing : ℝ) := by
    push_cast
    rfl
  rw [originEqual,widthEqual] at firstContains lastContains
  apply RealRectangleBoundary.ports_eq_of_same_side _ _ _ _ sameSide firstContains lastContains
  · exact integer_ne_perturbed_cut column segment.start.1 epsilonPositive epsilonSmall false
  · have cut := integer_ne_perturbed_cut ((column : Int)+1) segment.start.1 epsilonPositive epsilonSmall true
    intro equal
    apply cut
    simp only [Prod.fst,Int.cast_add,Int.cast_natCast,Int.cast_one,ite_true] at equal ⊢
    linarith
  · simpa using integer_ne_perturbed_cut 0 segment.start.2 (seamPerturbation_positive graph drawing) (seamPerturbation_lt_one graph drawing) true
  · have cut := integer_ne_perturbed_cut drawing.gridSize segment.start.2 (seamPerturbation_positive graph drawing) (seamPerturbation_lt_one graph drawing) true
    intro equal
    apply cut
    simp only [Prod.snd,Int.cast_natCast,ite_true] at equal ⊢
    linarith

theorem rectanglePort_parent_tagged {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Nat} {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    ∃ tagged ∈ graph.edges.zipIdx, tagged.2 = key.parentKey.1 := by
  cases key with
  | vertical right key =>
    cases key with
    | crossing key =>
      obtain ⟨tagged,member,index,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp valid).1
      exact ⟨tagged,member,index⟩
    | incidence tagged target => exact ⟨tagged,valid.1,rfl⟩
  | horizontal top key =>
    have horizontal := (List.mem_filter.mp valid.1).1
    obtain ⟨tagged,member,index,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp horizontal).1
    exact ⟨tagged,member,index⟩

theorem rectanglePort_parent_interiors_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {first last : RectanglePortKey Vertex} (firstValid : first.Valid graph drawing column)
    (lastValid : last.Valid graph drawing column) (different : first.parentKey ≠ last.parentKey)
    {point : ℝ × ℝ} (firstContains : (drawing.liftedStraightSegment first.parentKey.1 first.parentKey.2).RealInteriorContains point)
    (lastContains : (drawing.liftedStraightSegment last.parentKey.1 last.parentKey.2).RealInteriorContains point) : False := by
  obtain ⟨firstTagged,firstMember,firstIndex⟩ := rectanglePort_parent_tagged firstValid
  obtain ⟨lastTagged,lastMember,lastIndex⟩ := rectanglePort_parent_tagged lastValid
  apply straight_lifted_interiors_disjoint planar firstMember lastMember (straight firstTagged firstMember) (straight lastTagged lastMember)
    first.parentKey.2 last.parentKey.2
  · simpa only [firstIndex,lastIndex,Prod.eta] using different
  · simpa only [firstIndex] using firstContains
  · simpa only [lastIndex] using lastContains

theorem rectanglePort_same_parent_unique_side {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {first last : RectanglePortKey Vertex} (firstValid : first.Valid graph drawing column)
    (lastValid : last.Valid graph drawing column) (sameParent : first.parentKey = last.parentKey)
    (sameSide : (first.virtualPort graph drawing column).side = (last.virtualPort graph drawing column).side) :
    first.virtualPort graph drawing column = last.virtualPort graph drawing column := by
  have firstContains := rectanglePort_parent_realInteriorContains planar straight column firstValid
  have lastContains := rectanglePort_parent_realInteriorContains planar straight column lastValid
  rw [← sameParent] at lastContains
  exact virtualSlab_ports_eq_of_same_side planar straight column sameSide
    (GridSegment.realInteriorContains_implies_realContains firstContains) (GridSegment.realInteriorContains_implies_realContains lastContains)

theorem rectanglePort_ne_of_parent_ne {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {first last : RectanglePortKey Vertex} (firstValid : first.Valid graph drawing column)
    (lastValid : last.Valid graph drawing column) (different : first.parentKey ≠ last.parentKey) :
    first.virtualPort graph drawing column ≠ last.virtualPort graph drawing column := by
  intro equal
  have firstContains := rectanglePort_parent_realInteriorContains planar straight column firstValid
  have lastContains := rectanglePort_parent_realInteriorContains planar straight column lastValid
  rw [equal] at firstContains
  exact rectanglePort_parent_interiors_disjoint planar straight firstValid lastValid different firstContains lastContains

end LeanTrominoes.PeriodicGridDrawing
