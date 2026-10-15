/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleIntegralPortPositions
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryStripSeparation

/-! # A new cut-boundary point identifies its original integer cut and port face -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem rectanglePort_at_new_cut_boundary {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (line : Int) (right : Bool)
    {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (onCut : (rectangleLiftedPortPoint graph drawing column cell key).1 =
      (paddedRefinementFactor drawing.gridSize : Int)*line+
        (if right then -5 else 5)*crossingBound drawing.gridSize) :
    line = (column : Int)+(if right then 1 else 0)+(drawing.gridSize : Int)*cell.1 ∧
      ∃ raw : ColumnPortKey Vertex, key = .vertical right raw := by
  have faces := rectangleIntegralPort_point_bounds_faces planar degree graphLocal straight column valid
  have radiusPositive : (0 : Int) < crossingBound drawing.gridSize := by
    have positive : 0 < drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
    unfold crossingBound
    positivity
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    omega
  have lower : (paddedRefinementFactor drawing.gridSize : Int)*(drawing.rectangleRouteIndex column cell).1+
        5*crossingBound drawing.gridSize ≤ (rectangleLiftedPortPoint graph drawing column cell key).1 := by
    change _ ≤ (drawing.rectangleRouteOffset column cell).1+_
    simp only [rectangleRouteOffset,paddedSlabOrigin]
    linarith [faces.1.1]
  have upper : (rectangleLiftedPortPoint graph drawing column cell key).1 ≤
      (paddedRefinementFactor drawing.gridSize : Int)*((drawing.rectangleRouteIndex column cell).1+1)-5*crossingBound drawing.gridSize := by
    change (drawing.rectangleRouteOffset column cell).1+_ ≤ _
    simp only [rectangleRouteOffset,paddedSlabOrigin,paddedSlabWidth] at *
    nlinarith [faces.1.2]
  have strip : |((rectangleLiftedPortPoint graph drawing column cell key).1 : ℝ)-
      (paddedRefinementFactor drawing.gridSize : ℝ)*line| ≤ 5*(crossingBound drawing.gridSize : ℝ) := by
    rw [onCut]
    cases right <;> simp only [Bool.false_eq_true,if_false,if_true] <;> push_cast <;> apply abs_le.mpr <;> constructor <;> linarith
  have slab : (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.rectangleRouteIndex column cell).1+
        5*(crossingBound drawing.gridSize : ℝ) ≤ (rectangleLiftedPortPoint graph drawing column cell key).1 ∧
      ((rectangleLiftedPortPoint graph drawing column cell key).1 : ℝ) ≤
        (paddedRefinementFactor drawing.gridSize : ℝ)*((drawing.rectangleRouteIndex column cell).1+1)-5*(crossingBound drawing.gridSize : ℝ) := by
    exact ⟨by exact_mod_cast lower,by exact_mod_cast upper⟩
  have contact := strip_slab_contact_vertical_boundary spacing radiusPositive.le strip slab
  have lineEq : line = (drawing.rectangleRouteIndex column cell).1+(if right then 1 else 0) := by
    cases right
    · rcases contact with ⟨same,_⟩ | ⟨same,pointEq⟩
      · simpa using same
      · have oldEq : (rectangleLiftedPortPoint graph drawing column cell key).1 =
          (paddedRefinementFactor drawing.gridSize : Int)*(line)-5*crossingBound drawing.gridSize := by
          rw [same]
          exact_mod_cast pointEq
        simp only [Bool.false_eq_true,if_false] at onCut
        linarith
    · rcases contact with ⟨same,pointEq⟩ | ⟨same,_⟩
      · have oldEq : (rectangleLiftedPortPoint graph drawing column cell key).1 =
          (paddedRefinementFactor drawing.gridSize : Int)*line+5*crossingBound drawing.gridSize := by
          rw [same]
          exact_mod_cast pointEq
        simp only [if_true] at onCut
        linarith
      · simpa using same
  refine ⟨by dsimp only [rectangleRouteIndex] at lineEq; omega,rectanglePort_vertical_of_integral_face planar degree graphLocal straight column cell right valid ?_⟩
  rw [onCut,lineEq]
  cases right <;> simp [rectangleRouteOffset,paddedSlabOrigin,paddedSlabWidth]
  all_goals ring

end LeanTrominoes.PeriodicGridDrawing
