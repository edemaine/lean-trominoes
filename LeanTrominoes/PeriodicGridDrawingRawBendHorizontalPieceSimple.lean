/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendHorizontalPorts
import LeanTrominoes.GridPolylineRealJoinOpenSimple
import LeanTrominoes.GridPolylineRealOpenReverse

/-! # Simplicity of assembled nonvertical raw-piece routes -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem pieceSourceFan_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) : GridPolyline.IsRealOpenSimple (pieceSourceFan source drawing tagged) :=
  fanAt_simple planar (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor_positive drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).start (sourcePort_mem_allPorts _ member)

theorem pieceTargetFan_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) : GridPolyline.IsRealOpenSimple (pieceTargetFan source drawing tagged) :=
  (fanAt_simple planar (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor_positive drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).finish (targetPort_mem_allPorts _ member)).reverse

theorem piece_outer_fans_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (pieceSourceFan source drawing tagged) point) :
    ¬GridPolyline.RealContains (pieceTargetFan source drawing tagged) point := by
  intro lastContains
  have sourceSpacing : (20 : Int) < Cubic.coreFactor drawing.gridSize :=
    lt_trans (by norm_num) (Cubic.coreFactor_slope_spacing drawing.gridSize)
  have equal := fanAt_contacts_same_position source drawing sourceSpacing
    (Cubic.rasterFactor_positive drawing.gridSize) (sourcePort tagged.1 tagged.2) (targetPort tagged.1 tagged.2)
    firstContains ((GridPolyline.realContains_reverse _ _).mp lastContains)
  exact subdivision_segment_nonconstant planar member equal

theorem horizontal_pieceRoute_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) :
    GridPolyline.IsRealOpenSimple (pieceRoute source drawing tagged) := by
  have firstCore := GridPolyline.isRealOpenSimple_join (pieceSourceFan_simple planar member) (coreRoute_simple planar member)
    (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
    (fun _ firstContains coreContains => horizontal_coreRoute_sourceFan_contact planar degree member horizontal coreContains firstContains)
  apply GridPolyline.isRealOpenSimple_join firstCore (pieceTargetFan_simple planar member)
    (joinAtEndpoint_getLast? (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
      (coreRoute_endpoints source drawing tagged).2) (pieceTargetFan_head source drawing tagged)
  intro point joinedContains lastContains
  rcases (GridPolyline.realContains_join (pieceSourceFan_last source drawing tagged)
    (coreRoute_endpoints source drawing tagged).1 point).mp joinedContains with firstContains | coreContains
  · exact (piece_outer_fans_disjoint planar member firstContains lastContains).elim
  · exact horizontal_coreRoute_targetFan_contact planar degree member horizontal coreContains lastContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
