/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightEndpointRays
import LeanTrominoes.Common.Geometry.GridSegmentRealInteriorEndpoints

/-! # Distinct straight edge occurrences have disjoint real interiors -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem straight_lifted_interiors_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (secondMember : second ∈ graph.edges.zipIdx)
    (firstStraight : (drawing.edgeRoute first.2).length = 2) (secondStraight : (drawing.edgeRoute second.2).length = 2)
    (firstCell secondCell : Cell) (different : (first.2,firstCell) ≠ (second.2,secondCell))
    {point : ℝ × ℝ} (firstContains : (drawing.liftedStraightSegment first.2 firstCell).RealInteriorContains point)
    (secondContains : (drawing.liftedStraightSegment second.2 secondCell).RealInteriorContains point) : False := by
  have firstValid : first.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx firstMember
  have secondValid : second.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx secondMember
  have endpoints := (planar.2 first.2 second.2 firstCell secondCell firstValid secondValid different point
    ((realEdgeRoute_straight_image drawing first.2 firstCell firstStraight point).mpr
      (GridSegment.realInteriorContains_implies_realContains firstContains))
    ((realEdgeRoute_straight_image drawing second.2 secondCell secondStraight point).mpr
      (GridSegment.realInteriorContains_implies_realContains secondContains))).1
  have avoids := GridSegment.realInteriorContains_not_endpoints
    (liftedStraightSegment_nondegenerate planar.1 firstMember firstStraight firstCell) firstContains
  rcases (realEdgeRoute_straight_endpoints drawing first.2 firstCell firstStraight point).mp endpoints with start | finish
  · exact avoids.1 start
  · exact avoids.2 finish

end LeanTrominoes.PeriodicGridDrawing
