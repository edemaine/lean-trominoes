/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicColumnRefinement

/-! # Periodic crossing bars avoid connectors in every translated vertex cell -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem periodicColumnHeight_row_clearance {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {line : Int} {height : ℚ} (member : rationalResidue drawing.gridSize height ∈
      verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int))) :
    (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)*rationalCell drawing.gridSize height+10 <
      periodicColumnHeight graph drawing line height ∧
    periodicColumnHeight graph drawing line height <
      (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)*(rationalCell drawing.gridSize height+1)-10 := by
  have bounds := redistributedCrossingHeight_in_cell compatible degree member
  unfold periodicColumnHeight periodicRedistributedHeight
  constructor <;> nlinarith

theorem periodicColumnHeight_avoids_lifted_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ} (member : rationalResidue drawing.gridSize height ∈
      verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int))) {position : Cell}
    (positionMember : position ∈ drawing.vertexPositions) (vertexCell : Cell)
    (sameX : (Cell.add position (drawing.periodTranslation vertexCell)).1 = line) :
    10 < |periodicColumnHeight graph drawing line height-
      (refinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation vertexCell)).2| := by
  have inside := compatible.2.2.2.2.1 position positionMember
  have gridPositive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have spacing := refinementFactor_isolates_rectangles gridPositive
  have factorPositive : (0 : Int) < refinementFactor drawing.gridSize := by omega
  have outputPositive : (0 : Int) < OrthogonalDrawingRefinement.gridSize drawing.gridSize := by
    exact_mod_cast OrthogonalDrawingRefinement.gridSize_positive gridPositive
  have lineMod : line % (drawing.gridSize : Int) = position.1 := by
    rw [← sameX]
    simp only [Cell.add,periodTranslation,Cell.scale,Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt inside.1.le inside.2.1
  have scaled : (refinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation vertexCell)).2 =
      (refinementFactor drawing.gridSize : Int)*position.2+
        (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)*vertexCell.2 := by
    rw [OrthogonalDrawingRefinement.gridSize_eq_factor_mul]
    simp only [Cell.add,periodTranslation,Cell.scale,Nat.cast_mul]
    ring
  have lower : (refinementFactor drawing.gridSize : Int) ≤ (refinementFactor drawing.gridSize : Int)*position.2 := by
    nlinarith [inside.2.2.1]
  have upper : (refinementFactor drawing.gridSize : Int)*position.2 ≤
      (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)-(refinementFactor drawing.gridSize : Int) := by
    rw [OrthogonalDrawingRefinement.gridSize_eq_factor_mul]
    push_cast
    nlinarith [inside.2.2.2]
  rcases lt_trichotomy (rationalCell drawing.gridSize height) vertexCell.2 with before | same | after
  · have bounds := periodicColumnHeight_row_clearance compatible degree member
    have difference : periodicColumnHeight graph drawing line height-
        (refinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation vertexCell)).2 < -10 := by
      rw [scaled]
      nlinarith [bounds.2]
    rw [abs_of_neg (by omega)]
    omega
  · have gap := redistributedCrossingHeight_avoids_vertex compatible degree member positionMember lineMod.symm
    have difference : periodicColumnHeight graph drawing line height-
        (refinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation vertexCell)).2 =
        redistributedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height)-
          (refinementFactor drawing.gridSize : Int)*position.2 := by
      rw [scaled]
      unfold periodicColumnHeight periodicRedistributedHeight
      rw [same]
      ring
    rw [difference]
    exact gap
  · have bounds := periodicColumnHeight_row_clearance compatible degree member
    have difference : 10 < periodicColumnHeight graph drawing line height-
        (refinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation vertexCell)).2 := by
      rw [scaled]
      nlinarith [bounds.1]
    rw [abs_of_pos (by omega)]
    exact difference

theorem periodicCrossingBar_avoids_lifted_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ} (member : rationalResidue drawing.gridSize height ∈
      verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int))) {position : Cell}
    (positionMember : position ∈ drawing.vertexPositions) (vertexCell : Cell) (profile : AnchorProfile) (index : Fin 4)
    {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains
      (crossingBar (refinementFactor drawing.gridSize) line (periodicColumnHeight graph drawing line height)) point)
    (templateContains : GridPolyline.RealContains
      (rectangleTemplateAt (refinementFactor drawing.gridSize) (Cell.add position (drawing.periodTranslation vertexCell)) profile index) point) : False := by
  have gridPositive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have spacing := refinementFactor_isolates_rectangles gridPositive
  exact crossingBar_avoids_rectangle (by omega) profile index
    (periodicColumnHeight_avoids_lifted_vertex compatible degree member positionMember vertexCell) barContains templateContains

end LeanTrominoes.PeriodicGridDrawing
