/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCrossingEnumeration
import LeanTrominoes.Common.Geometry.GridSegmentRationalHorizontalCrossing

/-! # Finite complete tables of exact horizontal row-seam crossings -/
namespace LeanTrominoes.PeriodicGridDrawing

def horizontalCrossingCopies {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) : List (Nat × Cell) :=
  (nineEdgeCopies graph).filter fun key => decide
    ((drawing.liftedStraightSegment key.1 key.2).CrossesHorizontalLine line ∧
      0 ≤ (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line ∧
      (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line < (drawing.gridSize : ℚ))

def horizontalCrossingAbscissae {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) : Finset ℚ :=
  ((horizontalCrossingCopies graph drawing line).map
    fun key => (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line).toFinset

theorem horizontalCrossingAbscissae_card_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) (line : Int) :
    (horizontalCrossingAbscissae graph drawing line).card ≤ 18*drawing.gridSize^2 := by
  have finite := List.toFinset_card_le ((horizontalCrossingCopies graph drawing line).map
    fun key => (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line)
  have filtered := List.length_filter_le (fun key => decide
    ((drawing.liftedStraightSegment key.1 key.2).CrossesHorizontalLine line ∧
      0 ≤ (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line ∧
      (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line < (drawing.gridSize : ℚ))) (nineEdgeCopies graph)
  have copies := nineEdgeCopies_length graph
  have bound := nine_copy_edge_count_bound compatible degree
  unfold horizontalCrossingAbscissae horizontalCrossingCopies
  simp only [horizontalCrossingCopies,List.length_map] at finite
  omega

theorem horizontalCrossingCopies_complete {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1)
    {line : Int} (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize) (cell : Cell)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine line)
    (abscissaBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line < (drawing.gridSize : ℚ)) :
    (tagged.2,cell) ∈ horizontalCrossingCopies graph drawing line := by
  have segmentContains := GridSegment.rationalLineAbscissa_realContains crosses
  have routeContains := (realEdgeRoute_straight_image drawing tagged.2 cell straight _).mpr segmentContains
  have pointBounds : 0 ≤ ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line : ℝ) ∧
      ((drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa line : ℝ) ≤ drawing.gridSize ∧
      0 ≤ (line : ℝ) ∧ (line : ℝ) ≤ drawing.gridSize :=
    ⟨by exact_mod_cast abscissaBounds.1,by exact_mod_cast abscissaBounds.2.le,
      by exact_mod_cast lineBounds.1,by exact_mod_cast lineBounds.2⟩
  have neighbor := straight_realEdgeRoute_copy_window compatible member straight edgeLocal cell pointBounds routeContains
  exact List.mem_filter.mpr ⟨mem_nineEdgeCopies.mpr ⟨tagged,member,rfl,neighbor⟩,by simpa using And.intro crosses abscissaBounds⟩

theorem horizontal_crossing_abscissae_ne {drawing : PeriodicGridDrawing}
    (planar : drawing.RealRoutesMeetOnlyAtEndpoints) {firstIndex secondIndex : Nat}
    (firstValid : firstIndex < drawing.edgeRoutes.length) (secondValid : secondIndex < drawing.edgeRoutes.length)
    (firstStraight : (drawing.edgeRoute firstIndex).length = 2) (secondStraight : (drawing.edgeRoute secondIndex).length = 2)
    (firstCell secondCell : Cell) (different : (firstIndex,firstCell) ≠ (secondIndex,secondCell)) {line : Int}
    (firstCrosses : (drawing.liftedStraightSegment firstIndex firstCell).CrossesHorizontalLine line)
    (secondCrosses : (drawing.liftedStraightSegment secondIndex secondCell).CrossesHorizontalLine line) :
    (drawing.liftedStraightSegment firstIndex firstCell).rationalLineAbscissa line ≠
      (drawing.liftedStraightSegment secondIndex secondCell).rationalLineAbscissa line := by
  intro equal
  have firstContains := GridSegment.rationalLineAbscissa_realContains firstCrosses
  have secondContains := GridSegment.rationalLineAbscissa_realContains secondCrosses
  rw [← equal] at secondContains
  have endpoint := (planar firstIndex secondIndex firstCell secondCell firstValid secondValid different _
    ((realEdgeRoute_straight_image drawing firstIndex firstCell firstStraight _).mpr firstContains)
    ((realEdgeRoute_straight_image drawing secondIndex secondCell secondStraight _).mpr secondContains)).1
  have avoids := GridSegment.rationalLineAbscissa_not_endpoint firstCrosses
  rcases (realEdgeRoute_straight_endpoints drawing firstIndex firstCell firstStraight _).mp endpoint with start | finish
  · exact avoids.1 start
  · exact avoids.2 finish

end LeanTrominoes.PeriodicGridDrawing
