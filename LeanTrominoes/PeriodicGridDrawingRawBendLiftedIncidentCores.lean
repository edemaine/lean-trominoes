/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendOrientedCoreData
import LeanTrominoes.PeriodicGridDrawingRawBendIncidentCoreSeparation
import LeanTrominoes.PeriodicGridDrawingRawBendPeriodicCores
import LeanTrominoes.GridSegmentRealBoxTransforms

/-! # Actual incident core routes are disjoint in all periodic copies

Either endpoint can be the common vertex. The route itself is not reversed
or rasterized again: its image supplies the oriented tube and box bounds.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def coreTranslation (drawing : PeriodicGridDrawing) (copy : Cell) : Cell :=
  Cell.scale (Cubic.coreFactor drawing.gridSize) (drawing.periodTranslation copy)

def liftedIncidentRawSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) : GridSegment :=
  (incidentRawSegment source drawing tagged target).translate (drawing.periodTranslation copy)

def liftedIncidentAnchoredSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) : GridSegment :=
  (incidentAnchoredSegment source drawing tagged target).translate (coreTranslation drawing copy)

theorem coreRoute_incident_tube {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    ((incidentAnchoredSegment source drawing tagged target).scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point := by
  have tube : (cubicCore source drawing tagged).RealTubeContains 3 point := by
    unfold coreRoute at contains
    split_ifs at contains
    · exact ((cubicCore source drawing tagged).digitalRoute_tube contains).mono (by norm_num)
    · exact (cubicCore source drawing tagged).kickedDigitalRoute_tube
        (by rcases coreSide_unit source drawing tagged with side | side <;> rw [side] <;> norm_num)
        (by rcases coreSide_unit source drawing tagged with side | side <;> rw [side] <;> norm_num) contains
  cases target
  · exact tube
  · exact tube.reverse

theorem coreRoute_incident_box {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    ((incidentAnchoredSegment source drawing tagged target).scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point := by
  have box := coreRoute_box source drawing tagged contains
  cases target
  · exact box
  · exact box.reverse

theorem restoreCorePoint (drawing : PeriodicGridDrawing) (copy : Cell) (point : ℝ × ℝ) :
    ((Cubic.rasterFactor drawing.gridSize : ℝ)*(coreTranslation drawing copy).1+
        (point.1-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).1),
      (Cubic.rasterFactor drawing.gridSize : ℝ)*(coreTranslation drawing copy).2+
        (point.2-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).2)) = point := by
  apply Prod.ext <;> simp only [coreTranslation,cubicScale,periodTranslation,Cell.scale,Int.cast_mul,Int.cast_natCast] <;> ring

theorem liftedCoreRoute_incident_tube {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point) :
    ((liftedIncidentAnchoredSegment source drawing tagged target copy).scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have tube := coreRoute_incident_tube source drawing tagged target original
  have translated := tube.translate_scaled (coreTranslation drawing copy)
  simpa only [Int.cast_natCast,restoreCorePoint,liftedIncidentAnchoredSegment] using translated

theorem liftedCoreRoute_incident_box {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point) :
    ((liftedIncidentAnchoredSegment source drawing tagged target copy).scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have box := coreRoute_incident_box source drawing tagged target original
  have translated := box.translate_scaled (coreTranslation drawing copy)
  simpa only [Int.cast_natCast,restoreCorePoint,liftedIncidentAnchoredSegment] using translated

theorem liftedIncidentCoreData {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (target : Bool) (copy : Cell) : IncidentCoreData source drawing (incidentPort tagged target)
      (liftedIncidentRawSegment source drawing tagged target copy) (liftedIncidentAnchoredSegment source drawing tagged target copy) :=
  (incidentCoreData planar degree graphLocal drawingLocal member target).translate (drawing.periodTranslation copy)

theorem lifted_incident_coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstTarget secondTarget : Bool) (firstCopy secondCopy : Cell)
    (sameVertex : (incidentPort first firstTarget).vertex = (incidentPort second secondTarget).vertex)
    (sameStart : (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start =
      (liftedIncidentRawSegment source drawing second secondTarget secondCopy).start)
    (different : incidentPort first firstTarget ≠ incidentPort second secondTarget) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (liftedCoreRoute source drawing first firstCopy) point) :
    ¬GridPolyline.RealContains (liftedCoreRoute source drawing second secondCopy) point := by
  intro secondContains
  exact (liftedIncidentCoreData planar degree graphLocal drawingLocal firstMember firstTarget firstCopy).disjoint
    planar degree (liftedIncidentCoreData planar degree graphLocal drawingLocal secondMember secondTarget secondCopy)
    sameVertex sameStart different
    (liftedCoreRoute_incident_tube source drawing first firstTarget firstCopy firstContains)
    (liftedCoreRoute_incident_tube source drawing second secondTarget secondCopy secondContains)
    (liftedCoreRoute_incident_box source drawing first firstTarget firstCopy firstContains)
    (liftedCoreRoute_incident_box source drawing second secondTarget secondCopy secondContains)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
