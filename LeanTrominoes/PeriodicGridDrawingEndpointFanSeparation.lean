/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPaddedIncidenceIsolation
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow

/-! # The two endpoint fans of a nondegenerate straight edge are disjoint -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem endpoint_fans_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {point : ℝ × ℝ}
    (sourceContains : GridPolyline.RealContains (paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2)) point)
    (targetContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset) point) : False := by
  have sourceRaw : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2) (0,0)) point := by
    rw [liftedPaddedIncidenceRoute_eq_translate]
    simpa [Cell.scale,translatePolyline_zero] using sourceContains
  have contact := liftedPaddedIncidenceRoutes_contact planar.1.1 (distinctPortRayKeys_of_planar_straight planar straight) degree
    (sourcePort_mem_allPorts graph member) (targetPort_mem_allPorts graph member) (0,0) tagged.1.offset sourceRaw targetContains
  have vertices : tagged.1.source = tagged.1.target := contact.1
  have offset : tagged.1.offset = (0,0) := contact.2.1.symm
  have sourceEq := liftedStraightSegment_start planar.1.1 member (0,0)
  have targetEq := liftedStraightSegment_finish planar.1.1 member (0,0)
  have nondegenerate := liftedStraightSegment_nondegenerate planar.1 member (straight _ member) (0,0)
  apply nondegenerate
  rw [sourceEq,targetEq,vertices,offset]
  simp [Cell.add]

end LeanTrominoes.PeriodicGridDrawing
