/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentScaledIntegerNeighborhood
import LeanTrominoes.PeriodicGridDrawingPaddedIncidenceIsolation
import LeanTrominoes.PeriodicGridDrawingStraightSegments
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow

/-! # A scaled vertical segment can approach a vertex fan only at an incident old vertex -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem scaled_vertical_segment_fan_contact_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeCell : Cell)
    (vertical : (drawing.liftedStraightSegment tagged.2 edgeCell).start.1 =
      (drawing.liftedStraightSegment tagged.2 edgeCell).finish.1)
    {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell)
    {point : ℝ × ℝ}
    (segmentContains : ((drawing.liftedStraightSegment tagged.2 edgeCell).scale (paddedRefinementFactor drawing.gridSize)).RealContains point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell) =
        (drawing.liftedStraightSegment tagged.2 edgeCell).start ∨
      Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell) =
        (drawing.liftedStraightSegment tagged.2 edgeCell).finish := by
  have oldVertical : (drawing.liftedStraightSegment tagged.2 edgeCell).IsVertical := by
    refine ⟨vertical,?_⟩
    intro same
    exact liftedStraightSegment_nondegenerate valid member straight edgeCell (Prod.ext vertical same)
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have bounds := enlargedRectangleTemplate_real_bounds _ _ _ _ _ fanContains
  have near : |point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*
        (Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell)).1| ≤ (10*(crossingBound drawing.gridSize : Int) : Int) ∧
      |point.2-(paddedRefinementFactor drawing.gridSize : ℝ)*
        (Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell)).2| ≤ (10*(crossingBound drawing.gridSize : Int) : Int) := by
    push_cast
    have nonnegative : (0 : ℝ) ≤ crossingBound drawing.gridSize := by positivity
    exact ⟨bounds.1.trans (by linarith),bounds.2⟩
  have oldContains := GridSegment.scaled_vertical_neighborhood_contact_implies_incident oldVertical
    (by positivity : (0 : Int) ≤ 10*(crossingBound drawing.gridSize : Int)) spacing near segmentContains
  have vertexMember := valid.1.vertexPosition_mem (port_vertex_mem valid.1.1 portMember)
  have indexValid : tagged.2 < drawing.edgeRoutes.length := by
    rw [valid.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx member
  have oldEndpoint := valid.2.2 _ vertexMember fanCell edgeCell tagged.2 indexValid
    ((realEdgeRoute_straight_image drawing tagged.2 edgeCell straight _).mpr (GridSegment.realContains_of_contains oldContains))
  have ends := (realEdgeRoute_straight_endpoints drawing tagged.2 edgeCell straight _).mp oldEndpoint
  rcases ends with source | target
  · exact Or.inl (realCell_injective source)
  · exact Or.inr (realCell_injective target)

end LeanTrominoes.PeriodicGridDrawing
