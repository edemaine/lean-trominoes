/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendIncidentFanContacts

/-! # Incident fan contact bounds in every periodic copy -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem fanAt_translate_center {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center offset : Cell) (port : GraphPort (Vertex V)) :
    fanAt source drawing factor raster (Cell.add offset center) port =
      translatePolyline (Cell.scale ((raster : Int)*factor) offset) (fanAt source drawing factor raster center port) := by
  simp only [fanAt,translatePolyline,List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp only [Function.comp_def,Cell.add,Cell.scale] <;> ring

theorem cubic_period_scale (drawing : PeriodicGridDrawing) (copy : Cell) :
    Cell.scale (cubicScale drawing*drawing.gridSize) copy =
      Cell.scale ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int)) (drawing.periodTranslation copy) := by
  apply Prod.ext <;> simp only [cubicScale,periodTranslation,Cell.scale] <;> ring

theorem lifted_scaled_incident_start {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) :
    ((liftedIncidentAnchoredSegment source drawing tagged target copy).scale (Cubic.rasterFactor drawing.gridSize)).start =
      Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy)
        (((incidentAnchoredSegment source drawing tagged target).scale (Cubic.rasterFactor drawing.gridSize)).start) := by
  apply Prod.ext <;> simp only [liftedIncidentAnchoredSegment,coreTranslation,cubicScale,periodTranslation,
    GridSegment.translate,GridSegment.scale,Cell.add,Cell.scale] <;> ring

theorem liftedCoreRoute_incidentFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (target : Bool) (copy : Cell) (otherPort : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point)
    (fanContains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (liftedIncidentRawSegment source drawing tagged target copy).start otherPort) point) :
    point = realCell ((liftedIncidentAnchoredSegment source drawing tagged target copy).scale (Cubic.rasterFactor drawing.gridSize)).start := by
  have originalCore := (GridPolyline.realContains_translate_inverse _ _ _).mp coreContains
  change GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (Cell.add (drawing.periodTranslation copy) (incidentRawSegment source drawing tagged target).start) otherPort) point at fanContains
  rw [fanAt_translate_center,← cubic_period_scale] at fanContains
  have originalFan := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  have contact := coreRoute_incidentFan_contact planar degree graphLocal drawingLocal member target otherPort originalCore originalFan
  rw [lifted_scaled_incident_start]
  have x := congrArg Prod.fst contact
  have y := congrArg Prod.snd contact
  apply Prod.ext <;> simp only [realCell,Cell.add,Int.cast_add] at x y ⊢ <;> linarith

theorem liftedCoreRoute_avoids_other_incident_fan {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (target : Bool) (copy : Cell) {otherPort : GraphPort (Vertex V)}
    (otherMember : otherPort ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : (incidentPort tagged target).vertex = otherPort.vertex)
    (different : incidentPort tagged target ≠ otherPort) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point) :
    ¬GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (liftedIncidentRawSegment source drawing tagged target copy).start otherPort) point := by
  intro fanContains
  have originalCore := (GridPolyline.realContains_translate_inverse _ _ _).mp coreContains
  change GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (Cell.add (drawing.periodTranslation copy) (incidentRawSegment source drawing tagged target).start) otherPort) point at fanContains
  rw [fanAt_translate_center,← cubic_period_scale] at fanContains
  have originalFan := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  exact coreRoute_avoids_other_incident_fan planar degree graphLocal drawingLocal member target otherMember sameVertex different originalCore originalFan

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
