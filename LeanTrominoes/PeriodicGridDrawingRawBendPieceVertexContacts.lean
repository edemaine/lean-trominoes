/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendCoreFanContactIdentification
import LeanTrominoes.PeriodicGridDrawingRawBendLiftedPieceRoutes
import LeanTrominoes.GridPolylineRealEndpointContainment

/-! # Scaled raw vertices can meet full cubic pieces only at their endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem liftedPieceRoute_vertex_contact {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (graphLocal : source.IsLocal)
    (drawingLocal : drawing.IsRealLocal source) {vertex : Vertex V}
    (vertexMember : vertex ∈ (subdivisionGraph source drawing).vertices)
    {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) (copy vertexCopy : Cell)
    (contains : GridPolyline.RealContains (liftedPieceRoute source drawing tagged copy)
      (realCell (Cell.scale (cubicScale drawing)
        (Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy))))) :
    (Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy)) =
        ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).start ∨
      (Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy)) =
        ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).finish := by
  classical
  let center := Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy)
  let port := sourcePort tagged.1 tagged.2
  have portMember := sourcePort_mem_allPorts (subdivisionGraph source drawing) member
  have auxiliaryFanContains : GridPolyline.RealContains
      (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize) center port)
      (realCell (Cell.scale (cubicScale drawing) center)) :=
    GridPolyline.realContains_head (fanAt_simple planar _ (Cubic.rasterFactor_positive _) center portMember).1
      (fanAt_head source drawing _ _ center port)
  have fanCase (target : Bool) (fanContains : GridPolyline.RealContains (liftedPieceFan source drawing tagged target copy)
      (realCell (Cell.scale (cubicScale drawing) center))) :
      center = (liftedIncidentRawSegment source drawing tagged target copy).start :=
    fanAt_contacts_same_position source drawing
      (by have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize; omega)
      (Cubic.rasterFactor_positive _) port (incidentPort tagged target) auxiliaryFanContains fanContains
  rcases (liftedPieceRoute_contains source drawing tagged copy _).mp contains with sourceFan | core | targetFan
  · exact Or.inl (fanCase false sourceFan)
  · by_cases rawContains : ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).RealContains (realCell center)
    · rcases raw_segment_vertex_contact planar vertexMember member copy vertexCopy rawContains with first | last
      · exact Or.inl (realCell_injective first)
      · exact Or.inr (realCell_injective last)
    · exact (liftedCoreRoute_avoids_nonincident_fan planar graphLocal drawingLocal member copy center port
        rawContains core auxiliaryFanContains).elim
  · exact Or.inr (fanCase true targetFan)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
