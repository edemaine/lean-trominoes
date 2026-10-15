/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightInteriorsDisjoint
import LeanTrominoes.Common.Geometry.GridSegmentRationalVerticalCrossing

/-! # A proper crossing point cannot touch another vertical edge -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem straight_vertical_avoids_crossing_point {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    {verticalEdge crossingEdge : PeriodicEdge Vertex × Nat}
    (verticalMember : verticalEdge ∈ graph.edges.zipIdx) (crossingMember : crossingEdge ∈ graph.edges.zipIdx)
    (verticalStraight : (drawing.edgeRoute verticalEdge.2).length = 2)
    (crossingStraight : (drawing.edgeRoute crossingEdge.2).length = 2)
    (verticalCell crossingCell : Cell)
    (vertical : (drawing.liftedStraightSegment verticalEdge.2 verticalCell).start.1 =
      (drawing.liftedStraightSegment verticalEdge.2 verticalCell).finish.1)
    {line : Int} (crosses : (drawing.liftedStraightSegment crossingEdge.2 crossingCell).CrossesVerticalLine line)
    (contains : (drawing.liftedStraightSegment verticalEdge.2 verticalCell).RealContains
      ((line : ℝ),((drawing.liftedStraightSegment crossingEdge.2 crossingCell).rationalLineHeight line : ℝ))) : False := by
  have different : (verticalEdge.2,verticalCell) ≠ (crossingEdge.2,crossingCell) := by
    intro same
    have indices := congrArg Prod.fst same
    have cells := congrArg Prod.snd same
    change verticalEdge.2 = crossingEdge.2 at indices
    change verticalCell = crossingCell at cells
    rw [← indices,← cells] at crosses
    rcases crosses with forward | backward <;> omega
  have verticalValid : verticalEdge.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx verticalMember
  have crossingValid : crossingEdge.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx crossingMember
  have endpoint := (planar.2 verticalEdge.2 crossingEdge.2 verticalCell crossingCell verticalValid crossingValid different _
    ((realEdgeRoute_straight_image drawing verticalEdge.2 verticalCell verticalStraight _).mpr contains)
    ((realEdgeRoute_straight_image drawing crossingEdge.2 crossingCell crossingStraight _).mpr
      (GridSegment.rationalLineHeight_realContains crosses))).2
  have avoids := GridSegment.rationalLineHeight_not_endpoint crosses
  rcases (realEdgeRoute_straight_endpoints drawing crossingEdge.2 crossingCell crossingStraight _).mp endpoint with first | last
  · exact avoids.1 first
  · exact avoids.2 last

end LeanTrominoes.PeriodicGridDrawing
