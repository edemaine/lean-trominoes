/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCrossingDistinctness
import LeanTrominoes.Graphs.Drawings.Orthogonal.FiniteHeightRedistribution

/-! # Computable order-preserving crossing redistribution on each vertex column -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def columnLevels (drawing : PeriodicGridDrawing) (line : Int) : Finset Int :=
  insert 0 (insert (drawing.gridSize : Int)
    (((drawing.vertexPositions.filter (fun point => decide (point.1 = line))).map Prod.snd).toFinset))

def redistributedCrossingHeight {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (height : ℚ) : Int :=
  redistributedHeight (drawing.columnLevels line) (verticalCrossingHeights graph drawing line) (crossingBound drawing.gridSize) height

theorem columnLevels_vertex {drawing : PeriodicGridDrawing} {line : Int} {point : Cell}
    (member : point ∈ drawing.vertexPositions) (sameX : point.1 = line) : point.2 ∈ drawing.columnLevels line := by
  simp only [columnLevels,Finset.mem_insert,List.mem_toFinset,List.mem_map]
  exact Or.inr (Or.inr ⟨point,List.mem_filter.mpr ⟨member,by simpa using sameX⟩,rfl⟩)

theorem columnLevels_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (line : Int) :
    ∀ level ∈ drawing.columnLevels line, 0 ≤ level ∧ level ≤ drawing.gridSize := by
  intro level member
  simp only [columnLevels,Finset.mem_insert,List.mem_toFinset,List.mem_map] at member
  rcases member with rfl | rfl | ⟨point,pointMember,rfl⟩
  · exact ⟨le_refl _,by positivity⟩
  · exact ⟨by positivity,le_refl _⟩
  · have inside := compatible.2.2.2.2.1 point (List.mem_filter.mp pointMember).1
    exact ⟨inside.2.2.1.le,inside.2.2.2.le⟩

theorem verticalCrossingHeight_bounds {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} {line : Int} {height : ℚ}
    (member : height ∈ verticalCrossingHeights graph drawing line) : 0 ≤ height ∧ height < drawing.gridSize := by
  obtain ⟨key,keyMember,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have filtered := (List.mem_filter.mp keyMember).2
  simp only [decide_eq_true_eq] at filtered
  exact filtered.2

theorem column_bracket_present {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} {line : Int} {height : ℚ}
    (member : height ∈ verticalCrossingHeights graph drawing line) :
    (lowerLevels (drawing.columnLevels line) height).Nonempty ∧ (upperLevels (drawing.columnLevels line) height).Nonempty := by
  apply height_bracket_present_in_cell (grid := (drawing.gridSize : Int))
    (by simp [columnLevels]) (by simp [columnLevels])
  exact_mod_cast verticalCrossingHeight_bounds member

theorem redistributedCrossingHeights_strictMonoOn {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) (line : Int) :
    StrictMonoOn (redistributedCrossingHeight graph drawing line) (verticalCrossingHeights graph drawing line) := by
  apply redistributedHeight_strictMonoOn _ _ (fun _ member => column_bracket_present member)
  exact_mod_cast verticalCrossingHeights_card_bound compatible degree line

theorem redistributedCrossingHeight_in_cell {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (member : height ∈ verticalCrossingHeights graph drawing line) :
    10 < redistributedCrossingHeight graph drawing line height ∧
      redistributedCrossingHeight graph drawing line height < (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int)-10 := by
  have present := column_bracket_present member
  have countBound : ((verticalCrossingHeights graph drawing line).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast verticalCrossingHeights_card_bound compatible degree line
  have bounds := redistributedHeight_bounds member present.1 present.2 countBound
  have lowerBound := (columnLevels_bounds compatible line _ (lowerHeight_spec present.1).1).1
  have upperBound := (columnLevels_bounds compatible line _ (upperHeight_spec present.2).1).2
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have lower := vertexCoordinate_monotone nonnegative lowerBound
  have upper := vertexCoordinate_monotone nonnegative upperBound
  have zero : vertexCoordinate (crossingBound drawing.gridSize : Int) 0 = 0 := by simp [vertexCoordinate]
  have top : vertexCoordinate (crossingBound drawing.gridSize : Int) drawing.gridSize =
      (OrthogonalDrawingRefinement.gridSize drawing.gridSize : Int) := by
    rw [vertexCoordinate_eq_factor,gridSize_eq_factor_mul]
    push_cast
    rfl
  change 10 < redistributedHeight _ _ _ _ ∧ redistributedHeight _ _ _ _ < _
  rw [zero] at lower
  rw [top] at upper
  constructor <;> omega

theorem verticalCrossingHeight_ne_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (edgeMember : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line)
    {point : Cell} (pointMember : point ∈ drawing.vertexPositions) (sameX : point.1 = line) :
    (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line ≠ (point.2 : ℚ) := by
  intro equal
  have segmentContains := GridSegment.rationalLineHeight_realContains crosses
  have routeContains := (realEdgeRoute_straight_image drawing tagged.2 cell straight _).mpr segmentContains
  have pointEq : ((line : ℝ),((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line : ℝ)) = realCell point := by
    rw [equal]
    simp only [← sameX,Rat.cast_intCast,realCell]
  have atVertex : GridPolyline.RealContains (drawing.realEdgeRoute tagged.2 cell) (realCell point) := by
    rw [pointEq] at routeContains
    exact routeContains
  have indexValid : tagged.2 < drawing.edgeRoutes.length := by
    rw [valid.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx edgeMember
  have endpoint := valid.2.2 point pointMember (0,0) cell tagged.2 indexValid
    (by simpa [periodTranslation,Cell.scale,Cell.add] using atVertex)
  have endpoints := (realEdgeRoute_straight_endpoints drawing tagged.2 cell straight _).mp endpoint
  have avoids := GridSegment.rationalLineHeight_not_endpoint crosses
  rcases endpoints with first | last
  · exact avoids.1 (pointEq.trans (by simpa [periodTranslation,Cell.scale,Cell.add,realCell] using first))
  · exact avoids.2 (pointEq.trans (by simpa [periodTranslation,Cell.scale,Cell.add,realCell] using last))

end LeanTrominoes.PeriodicGridDrawing
