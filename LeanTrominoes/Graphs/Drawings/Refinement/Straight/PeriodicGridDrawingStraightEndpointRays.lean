/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationEndpointRays
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightSegments
import LeanTrominoes.Common.Geometry.GridSegmentStraightRayKeys

/-! # Outward straight segments at prototype vertices -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing GeneralVertexNormalization

def outwardStraightSegment {Vertex : Type*} (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target : Bool) : GridSegment :=
  let segment := drawing.liftedStraightSegment tagged.2 (endpointCell tagged target)
  if target then segment.reverse else segment

theorem straightSegment_nondegenerate {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) :
    (drawing.straightSegment tagged.2).start ≠ (drawing.straightSegment tagged.2).finish := by
  have simple := valid.2.1 _ (edgeRoute_mem_of_compatible valid.1 member)
  obtain ⟨first,second,routeEq⟩ := List.length_eq_two.mp straight
  simpa [straightSegment,routeEq] using simple.2.1 ⟨first,second⟩ (by simp [routeEq,gridPolylineSegments])

theorem liftedStraightSegment_nondegenerate {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (cell : Cell) :
    (drawing.liftedStraightSegment tagged.2 cell).start ≠ (drawing.liftedStraightSegment tagged.2 cell).finish := by
  intro equal
  have hx := congrArg Prod.fst equal
  have hy := congrArg Prod.snd equal
  simp [liftedStraightSegment,GridSegment.translate,Cell.add] at hx hy
  exact straightSegment_nondegenerate valid member straight (Prod.ext hx hy)

theorem outwardStraightSegment_nondegenerate {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (target : Bool) :
    (drawing.outwardStraightSegment tagged target).start ≠ (drawing.outwardStraightSegment tagged target).finish := by
  cases target
  · exact liftedStraightSegment_nondegenerate valid member straight _
  · exact (liftedStraightSegment_nondegenerate valid member straight _).symm

theorem outwardStraightSegment_start {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target : Bool) :
    (drawing.outwardStraightSegment tagged target).start =
      drawing.vertexPosition graph (endpointPort tagged target).vertex := by
  have routeMatches := compatible.2.2.2.2.2 tagged member
  cases target <;> apply Prod.ext <;>
    simp [outwardStraightSegment,liftedStraightSegment,straightSegment,endpointPort,endpointCell,
      sourcePort,targetPort,GridSegment.reverse,GridSegment.translate,routeMatches.1,routeMatches.2,
      periodTranslation,Cell.add,Cell.scale] <;> ring

theorem outwardStraightSegment_image {Vertex : Type*} (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target : Bool)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (point : ℝ × ℝ) :
    (drawing.outwardStraightSegment tagged target).RealContains point ↔
      GridPolyline.RealContains (drawing.realEdgeRoute tagged.2 (endpointCell tagged target)) point := by
  cases target
  · exact (realEdgeRoute_straight_image drawing tagged.2 _ straight point).symm
  · exact (GridSegment.realContains_reverse _ _).trans
      (realEdgeRoute_straight_image drawing tagged.2 _ straight point).symm

theorem outwardStraightSegment_same_key_same_occurrence {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aStraight : (drawing.edgeRoute a.2).length = 2) (bStraight : (drawing.edgeRoute b.2).length = 2)
    (aTarget bTarget : Bool) (sameVertex : (endpointPort a aTarget).vertex = (endpointPort b bTarget).vertex)
    (sameKey : (drawing.outwardStraightSegment a aTarget).straightRayKey =
      (drawing.outwardStraightSegment b bTarget).straightRayKey) :
    (a.2,endpointCell a aTarget) = (b.2,endpointCell b bTarget) := by
  by_contra different
  have firstContains := GridSegment.realContains_straightRay_halfStep
    (outwardStraightSegment_nondegenerate planar.1 am aStraight aTarget)
  have secondContains := GridSegment.realContains_straightRay_halfStep
    (outwardStraightSegment_nondegenerate planar.1 bm bStraight bTarget)
  rw [outwardStraightSegment_start planar.1.1 am aTarget] at firstContains
  rw [outwardStraightSegment_start planar.1.1 bm bTarget,← sameVertex,← sameKey] at secondContains
  have firstValid : a.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx am
  have secondValid : b.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx bm
  have endpoints := (planar.2 a.2 b.2 (endpointCell a aTarget) (endpointCell b bTarget)
    firstValid secondValid different _
    ((outwardStraightSegment_image drawing a aTarget aStraight _).mp firstContains)
    ((outwardStraightSegment_image drawing b bTarget bStraight _).mp secondContains)).1
  rcases (realEdgeRoute_straight_endpoints drawing a.2 _ aStraight _).mp endpoints with first | last
  · exact StraightRayKey.halfStep_not_integral _ _ _ first
  · exact StraightRayKey.halfStep_not_integral _ _ _ last

end LeanTrominoes.PeriodicGridDrawing
