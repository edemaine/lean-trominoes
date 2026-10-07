/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingColumnRefinement
import LeanTrominoes.FiniteHeightPaddedRedistribution

/-! # Column crossing heights with room for enlarged connectors and seam arcs -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def paddedCrossingHeight {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (height : ℚ) : Int :=
  paddedRedistributedHeight (drawing.columnLevels line) (verticalCrossingHeights graph drawing line)
    (crossingBound drawing.gridSize) height

theorem paddedCrossingHeights_strictMonoOn {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) (line : Int) :
    StrictMonoOn (paddedCrossingHeight graph drawing line) (verticalCrossingHeights graph drawing line) := by
  apply paddedRedistributedHeight_strictMonoOn _ _ (fun _ member => column_bracket_present member)
  exact_mod_cast verticalCrossingHeights_card_bound compatible degree line

theorem paddedCrossingHeight_in_cell {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (member : height ∈ verticalCrossingHeights graph drawing line) :
    30*(crossingBound drawing.gridSize : Int)+10 < paddedCrossingHeight graph drawing line height ∧
      paddedCrossingHeight graph drawing line height < (paddedGridSize drawing.gridSize : Int)-(30*crossingBound drawing.gridSize+10) := by
  have present := column_bracket_present member
  have countBound : ((verticalCrossingHeights graph drawing line).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast verticalCrossingHeights_card_bound compatible degree line
  have bounds := paddedRedistributedHeight_bounds member present.1 present.2 countBound
  have lowerBound := (columnLevels_bounds compatible line _ (lowerHeight_spec present.1).1).1
  have upperBound := (columnLevels_bounds compatible line _ (upperHeight_spec present.2).1).2
  have nonnegative : (0 : Int) ≤ 3*(crossingBound drawing.gridSize : Int) := by positivity
  have lower := vertexCoordinate_monotone nonnegative lowerBound
  have upper := vertexCoordinate_monotone nonnegative upperBound
  have zero : vertexCoordinate (3*(crossingBound drawing.gridSize : Int)) 0 = 0 := by simp [vertexCoordinate]
  have top : vertexCoordinate (3*(crossingBound drawing.gridSize : Int)) drawing.gridSize = (paddedGridSize drawing.gridSize : Int) := by
    rw [padded_vertexCoordinate_eq_factor]
    simp only [paddedGridSize,Nat.cast_mul]
  change _ < paddedRedistributedHeight _ _ _ _ ∧ paddedRedistributedHeight _ _ _ _ < _
  rw [zero] at lower
  rw [top] at upper
  constructor <;> omega

theorem paddedCrossingHeight_below_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ} {point : Cell}
    (member : height ∈ verticalCrossingHeights graph drawing line)
    (pointMember : point ∈ drawing.vertexPositions) (sameX : point.1 = line) (below : height < (point.2 : ℚ)) :
    paddedCrossingHeight graph drawing line height < (paddedRefinementFactor drawing.gridSize : Int)*point.2-
      (30*crossingBound drawing.gridSize+10) := by
  have present := column_bracket_present member
  have countBound : ((verticalCrossingHeights graph drawing line).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast verticalCrossingHeights_card_bound compatible degree line
  simpa only [paddedCrossingHeight,padded_vertexCoordinate_eq_factor] using paddedRedistributedHeight_below_vertex
    member present.1 present.2 countBound (columnLevels_vertex pointMember sameX) below

theorem paddedCrossingHeight_above_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ} {point : Cell}
    (member : height ∈ verticalCrossingHeights graph drawing line)
    (pointMember : point ∈ drawing.vertexPositions) (sameX : point.1 = line) (above : (point.2 : ℚ) ≤ height) :
    (paddedRefinementFactor drawing.gridSize : Int)*point.2+(30*crossingBound drawing.gridSize+10) <
      paddedCrossingHeight graph drawing line height := by
  have present := column_bracket_present member
  have countBound : ((verticalCrossingHeights graph drawing line).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast verticalCrossingHeights_card_bound compatible degree line
  simpa only [paddedCrossingHeight,padded_vertexCoordinate_eq_factor] using paddedRedistributedHeight_above_vertex
    member present.1 present.2 countBound (columnLevels_vertex pointMember sameX) above

end LeanTrominoes.PeriodicGridDrawing
