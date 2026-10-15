/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedFanContacts
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendPieceSimplicity

/-! # Fan–core decomposition of full piece routes in all periodic copies -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def liftedPieceFan {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) : List Cell :=
  fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (liftedIncidentRawSegment source drawing tagged target copy).start (incidentPort tagged target)

noncomputable def liftedPieceRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (copy : Cell) : List Cell :=
  translatePolyline (Cell.scale (cubicScale drawing*drawing.gridSize) copy) (pieceRoute source drawing tagged)

theorem liftedPieceFan_eq_translate {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) :
    liftedPieceFan source drawing tagged target copy =
      translatePolyline (Cell.scale (cubicScale drawing*drawing.gridSize) copy)
        (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
          (incidentRawSegment source drawing tagged target).start (incidentPort tagged target)) := by
  change fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (Cell.add (drawing.periodTranslation copy) (incidentRawSegment source drawing tagged target).start) (incidentPort tagged target) = _
  rw [fanAt_translate_center,← cubic_period_scale]

theorem liftedPieceFan_contains {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealContains (liftedPieceFan source drawing tagged target copy) point ↔
      GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
        (incidentRawSegment source drawing tagged target).start (incidentPort tagged target))
        (point.1-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).1,
          point.2-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).2) := by
  rw [liftedPieceFan_eq_translate]
  exact GridPolyline.realContains_translate_inverse _ _ _

theorem liftedPieceRoute_contains {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (copy : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealContains (liftedPieceRoute source drawing tagged copy) point ↔
      GridPolyline.RealContains (liftedPieceFan source drawing tagged false copy) point ∨
      GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point ∨
      GridPolyline.RealContains (liftedPieceFan source drawing tagged true copy) point := by
  rw [liftedPieceRoute,GridPolyline.realContains_translate_inverse,pieceRoute_contains,
    liftedPieceFan_contains,liftedCoreRoute,GridPolyline.realContains_translate_inverse,liftedPieceFan_contains]
  simp only [pieceSourceFan,pieceTargetFan,incidentRawSegment,incidentPort,ite_true,Bool.false_eq_true,ite_false,GridSegment.reverse,
    GridPolyline.realContains_reverse]

theorem liftedPieceRoute_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) (copy : Cell) :
    GridPolyline.IsRealOpenSimple (liftedPieceRoute source drawing tagged copy) := (pieceRoute_simple planar degree member).translate _

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
