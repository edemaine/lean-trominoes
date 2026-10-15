/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleIntegralPortPositions
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceIntervalSeparation
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundarySlabSeparation

/-! # New ports in distinct rectangles can coincide only on the same original row seam -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting RationalIntegerStripCover

theorem rectangleIntegralPort_new_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (0 ≤ (rectangleLiftedPortPoint graph drawing column cell key).1-(drawing.rectangleRouteOffset column cell).1 ∧
      (rectangleLiftedPortPoint graph drawing column cell key).1-(drawing.rectangleRouteOffset column cell).1 ≤ drawing.paddedSlabWidth) ∧
    RowContains (paddedGridSize drawing.gridSize : ℚ) 0 cell.2
      (rectangleLiftedPortPoint graph drawing column cell key).2 := by
  have bounds := rectangleIntegralPort_point_bounds_faces planar degree graphLocal straight column valid
  unfold rectangleLiftedPortPoint RowContains
  simp only [Cell.add,rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex]
  push_cast
  have lower : (0 : ℚ) ≤ ((key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)).2 := by
    exact_mod_cast bounds.2.1.1
  have upper : (((key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)).2 : ℚ) ≤ paddedGridSize drawing.gridSize := by
    exact_mod_cast bounds.2.1.2
  refine ⟨⟨by linarith [bounds.1.1],by linarith [bounds.1.2]⟩,by linarith,by linarith⟩

set_option maxRecDepth 2048 in
theorem rectangle_distinct_integral_ports_old_y_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) {first last : RectanglePortKey Vertex}
    (firstValid : first.Valid graph drawing firstColumn) (lastValid : last.Valid graph drawing lastColumn)
    (different : (firstColumn,firstCell) ≠ (lastColumn,lastCell))
    (pointEq : rectangleLiftedPortPoint graph drawing firstColumn firstCell first =
      rectangleLiftedPortPoint graph drawing lastColumn lastCell last) :
    (rectanglePortOriginalPoint graph drawing firstColumn firstCell first).2 =
      (rectanglePortOriginalPoint graph drawing lastColumn lastCell last).2 ∧
      ∃ top raw, first = .horizontal top raw := by
  have firstBounds := rectangleIntegralPort_new_bounds planar degree graphLocal straight firstColumn firstCell firstValid
  have lastBounds := rectangleIntegralPort_new_bounds planar degree graphLocal straight lastColumn lastCell lastValid
  have pointX := congrArg Prod.fst pointEq
  have pointY := congrArg Prod.snd pointEq
  have pitchPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have radiusPositive : (0 : Int) < crossingBound drawing.gridSize := by
    have positive : 0 < drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
    unfold crossingBound
    positivity
  have gap : drawing.paddedSlabWidth < (paddedRefinementFactor drawing.gridSize : Int) := by unfold paddedSlabWidth; omega
  have columns : (firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1 =
      (lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1 := by
    by_contra differentColumns
    have firstX := firstBounds.1
    have lastX := lastBounds.1
    simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex] at firstX lastX
    rw [← pointX] at lastX
    apply separated_closed_bands_disjoint (point := ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-5*(crossingBound drawing.gridSize : ℝ))
      pitchPositive gap differentColumns
    · have lower : (0 : ℝ) ≤ ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1)+5*(crossingBound drawing.gridSize : ℝ)) := by exact_mod_cast firstX.1
      have upper : ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((firstColumn : Int)+(drawing.gridSize : Int)*firstCell.1)+5*(crossingBound drawing.gridSize : ℝ)) ≤ drawing.paddedSlabWidth := by exact_mod_cast firstX.2
      push_cast at lower upper ⊢
      constructor <;> linarith only [lower,upper]
    · have lower : (0 : ℝ) ≤ ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1)+5*(crossingBound drawing.gridSize : ℝ)) := by exact_mod_cast lastX.1
      have upper : ((rectangleLiftedPortPoint graph drawing firstColumn firstCell first).1 : ℝ)-
          ((paddedRefinementFactor drawing.gridSize : ℝ)*((lastColumn : Int)+(drawing.gridSize : Int)*lastCell.1)+5*(crossingBound drawing.gridSize : ℝ)) ≤ drawing.paddedSlabWidth := by exact_mod_cast lastX.2
      push_cast at lower upper ⊢
      constructor <;> linarith only [lower,upper]
  have indices := rectangle_piece_index_eq firstBound lastBound (firstCell := (firstCell.1,0)) (lastCell := (lastCell.1,0)) columns rfl
  have projected := congrArg Prod.fst indices.2
  have cellX : firstCell.1 = lastCell.1 := projected
  have differentRows : firstCell.2 ≠ lastCell.2 := fun equal => different (Prod.ext indices.1 (Prod.ext cellX equal))
  have room := paddedSlab_room drawing
  have heightPositive : (0 : ℚ) < paddedGridSize drawing.gridSize := by exact_mod_cast (by omega : (0 : Int) < paddedGridSize drawing.gridSize)
  rw [← pointY] at lastBounds
  rcases closed_row_contact_cases heightPositive firstBounds.2 lastBounds.2 with same | ⟨adjacent,seam⟩ | ⟨adjacent,seam⟩
  · exact (differentRows same).elim
  · have firstFace : (rectangleLiftedPortPoint graph drawing firstColumn firstCell first).2 =
        (drawing.rectangleRouteOffset firstColumn firstCell).2+(paddedGridSize drawing.gridSize : Int) := by
      simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex]
      rw [adjacent] at seam
      push_cast at seam
      have castSeam : (rectangleLiftedPortPoint graph drawing firstColumn firstCell first).2 =
          (paddedGridSize drawing.gridSize : Int)*(firstCell.2+1)-0 := by exact_mod_cast seam
      nlinarith only [castSeam]
    have lastFace : (rectangleLiftedPortPoint graph drawing lastColumn lastCell last).2 =
        (drawing.rectangleRouteOffset lastColumn lastCell).2+0 := by
      rw [← pointY]
      simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex,add_zero]
      have clean := seam
      simp only [sub_zero] at clean
      exact_mod_cast clean
    obtain ⟨firstRaw,firstEq⟩ := rectanglePort_horizontal_of_integral_face planar degree graphLocal straight firstColumn firstCell true firstValid firstFace
    obtain ⟨lastRaw,lastEq⟩ := rectanglePort_horizontal_of_integral_face planar degree graphLocal straight lastColumn lastCell false lastValid lastFace
    refine ⟨?_,true,firstRaw,firstEq⟩
    rw [firstEq,lastEq,rectangle_horizontal_original_point_y,rectangle_horizontal_original_point_y,adjacent]
    simp
  · have firstFace : (rectangleLiftedPortPoint graph drawing firstColumn firstCell first).2 =
        (drawing.rectangleRouteOffset firstColumn firstCell).2+0 := by
      simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex,add_zero]
      have clean := seam
      simp only [sub_zero] at clean
      exact_mod_cast clean
    have lastFace : (rectangleLiftedPortPoint graph drawing lastColumn lastCell last).2 =
        (drawing.rectangleRouteOffset lastColumn lastCell).2+(paddedGridSize drawing.gridSize : Int) := by
      rw [← pointY]
      simp only [rectangleRouteOffset,paddedSlabOrigin,rectangleRouteIndex]
      rw [adjacent] at seam
      push_cast at seam
      have castSeam : (rectangleLiftedPortPoint graph drawing firstColumn firstCell first).2 =
          (paddedGridSize drawing.gridSize : Int)*(lastCell.2+1)-0 := by exact_mod_cast seam
      nlinarith only [castSeam]
    obtain ⟨firstRaw,firstEq⟩ := rectanglePort_horizontal_of_integral_face planar degree graphLocal straight firstColumn firstCell false firstValid firstFace
    obtain ⟨lastRaw,lastEq⟩ := rectanglePort_horizontal_of_integral_face planar degree graphLocal straight lastColumn lastCell true lastValid lastFace
    refine ⟨?_,false,firstRaw,firstEq⟩
    rw [firstEq,lastEq,rectangle_horizontal_original_point_y,rectangle_horizontal_original_point_y,adjacent]
    simp

end LeanTrominoes.PeriodicGridDrawing
