/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendHorizontalPieceSimple
import LeanTrominoes.PeriodicGridDrawingRawBendVerticalCoreContacts

/-! # Every assembled raw-piece route is simple and orthogonal -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem coreRoute_sourceFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (pieceSourceFan source drawing tagged) point) :
    point = realCell (cubicCore source drawing tagged).start := by
  by_cases vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0
  · exact vertical_coreRoute_sourceFan_contact planar degree member vertical coreContains fanContains
  · exact horizontal_coreRoute_sourceFan_contact planar degree member vertical coreContains fanContains

theorem coreRoute_targetFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (pieceTargetFan source drawing tagged) point) :
    point = realCell (cubicCore source drawing tagged).finish := by
  by_cases vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0
  · exact vertical_coreRoute_targetFan_contact planar degree member vertical coreContains fanContains
  · exact horizontal_coreRoute_targetFan_contact planar degree member vertical coreContains fanContains

theorem pieceRoute_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    GridPolyline.IsRealOpenSimple (pieceRoute source drawing tagged) := by
  have firstCore := GridPolyline.isRealOpenSimple_join (pieceSourceFan_simple planar member) (coreRoute_simple planar member)
    (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
    (fun _ firstContains coreContains => coreRoute_sourceFan_contact planar degree member coreContains firstContains)
  apply GridPolyline.isRealOpenSimple_join firstCore (pieceTargetFan_simple planar member)
    (joinAtEndpoint_getLast? (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
      (coreRoute_endpoints source drawing tagged).2) (pieceTargetFan_head source drawing tagged)
  intro point joinedContains lastContains
  rcases (GridPolyline.realContains_join (pieceSourceFan_last source drawing tagged)
    (coreRoute_endpoints source drawing tagged).1 point).mp joinedContains with firstContains | coreContains
  · exact (piece_outer_fans_disjoint planar member firstContains lastContains).elim
  · exact coreRoute_targetFan_contact planar degree member coreContains lastContains

theorem pieceRoute_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    GridPolyline.IsRealOpenSimple (pieceRoute source drawing tagged) ∧ OrthogonalPolyline (pieceRoute source drawing tagged) :=
  ⟨pieceRoute_simple planar degree member,pieceRoute_orthogonal planar member⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
