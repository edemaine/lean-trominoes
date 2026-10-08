/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleNewPortSeamContacts

/-! # Coincident integral ports have the same periodic column -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem rectangle_integral_ports_contact_columns {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) {first last : RectanglePortKey Vertex}
    (firstValid : first.Valid graph drawing firstColumn) (lastValid : last.Valid graph drawing lastColumn)
    (pointEq : rectangleLiftedPortPoint graph drawing firstColumn firstCell first =
      rectangleLiftedPortPoint graph drawing lastColumn lastCell last) :
    firstColumn = lastColumn ∧ firstCell.1 = lastCell.1 := by
  have firstBounds := (rectangleIntegralPort_new_bounds planar degree graphLocal straight firstColumn firstCell firstValid).1
  have lastBounds := (rectangleIntegralPort_new_bounds planar degree graphLocal straight lastColumn lastCell lastValid).1
  have pointX := congrArg Prod.fst pointEq
  have pitchPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have radiusPositive : (0 : Int) < crossingBound drawing.gridSize := by exact_mod_cast crossingBound_positive drawing
  have gap : drawing.paddedSlabWidth < (paddedRefinementFactor drawing.gridSize : Int) := by unfold paddedSlabWidth; omega
  have columns : (firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1 =
      (lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1 := by
    by_contra differentColumns
    simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex] at firstBounds lastBounds
    rw [← pointX] at lastBounds
    apply separated_closed_bands_disjoint (point := ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-5*(crossingBound drawing.gridSize : ℝ))
      pitchPositive gap differentColumns
    · have lower : (0 : ℝ) ≤ ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1)+5*(crossingBound drawing.gridSize : ℝ)) := by exact_mod_cast firstBounds.1
      have upper : ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1)+5*(crossingBound drawing.gridSize : ℝ)) ≤ drawing.paddedSlabWidth := by exact_mod_cast firstBounds.2
      push_cast at lower upper ⊢
      constructor <;> linarith only [lower,upper]
    · have lower : (0 : ℝ) ≤ ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1)+5*(crossingBound drawing.gridSize : ℝ)) := by exact_mod_cast lastBounds.1
      have upper : ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1)+5*(crossingBound drawing.gridSize : ℝ)) ≤ drawing.paddedSlabWidth := by exact_mod_cast lastBounds.2
      push_cast at lower upper ⊢
      constructor <;> linarith only [lower,upper]
  have indices := rectangle_piece_index_eq firstBound lastBound
    (firstCell := (firstCell.1,0)) (lastCell := (lastCell.1,0)) columns rfl
  have projected := congrArg Prod.fst indices.2
  exact ⟨indices.1,projected⟩

end LeanTrominoes.PeriodicGridDrawing
