/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendLiftedPieceRoutes
import LeanTrominoes.PeriodicGridDrawingRawBendCoreFanContactIdentification
import LeanTrominoes.PeriodicGridDrawingRawBendCoreSeparation

/-! # Full cubic piece routes meet only at their common graph endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem distinct_lifted_coreRoutes_avoid_pieceFan {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstCopy secondCopy : Cell) (target : Bool) (different : (first.2,firstCopy) ≠ (second.2,secondCopy))
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (liftedCoreRoute source drawing first firstCopy) point) :
    ¬GridPolyline.RealContains (liftedPieceFan source drawing second target secondCopy) point := by
  intro fanContains
  have secondData := incidentCoreData planar degree graphLocal drawingLocal secondMember target
  rw [liftedPieceFan,liftedIncidentRawSegment_start] at fanContains
  obtain ⟨firstTarget,portsEqual,copiesEqual,_⟩ := liftedCoreRoute_fan_contact_identifies_port planar degree graphLocal drawingLocal firstMember
    firstCopy (incidentCopy second target secondCopy) secondData.member coreContains fanContains
  have sameStart : (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start =
      (liftedIncidentRawSegment source drawing second target secondCopy).start := by
    rw [liftedIncidentRawSegment_start,liftedIncidentRawSegment_start,portsEqual,copiesEqual]
  exact lifted_incident_ports_ne planar firstMember secondMember firstTarget target firstCopy secondCopy sameStart different portsEqual

theorem distinct_lifted_pieceFans_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstTarget secondTarget : Bool) (firstCopy secondCopy : Cell) (different : (first.2,firstCopy) ≠ (second.2,secondCopy))
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (liftedPieceFan source drawing first firstTarget firstCopy) point)
    (secondContains : GridPolyline.RealContains (liftedPieceFan source drawing second secondTarget secondCopy) point) :
    point = realCell (Cell.scale (cubicScale drawing) (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start) ∧
      point = realCell (Cell.scale (cubicScale drawing) (liftedIncidentRawSegment source drawing second secondTarget secondCopy).start) := by
  have sameStart := fanAt_contacts_same_position source drawing
    (by have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize; omega)
    (Cubic.rasterFactor_positive drawing.gridSize) (incidentPort first firstTarget) (incidentPort second secondTarget) firstContains secondContains
  have sameVertex := (lifted_incident_start_unique planar firstMember secondMember firstTarget secondTarget firstCopy secondCopy sameStart).1
  have portsDifferent := lifted_incident_ports_ne planar firstMember secondMember firstTarget secondTarget firstCopy secondCopy sameStart different
  have firstData := incidentCoreData planar degree graphLocal drawingLocal firstMember firstTarget
  have secondData := incidentCoreData planar degree graphLocal drawingLocal secondMember secondTarget
  have secondAtFirst : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start (incidentPort second secondTarget)) point := by
    simpa only [liftedPieceFan,sameStart] using secondContains
  have contact := fanAt_contact_center planar degree (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor_positive drawing.gridSize)
    (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start firstData.member secondData.member sameVertex portsDifferent
    firstContains secondAtFirst
  exact ⟨contact,by simpa only [sameStart,cubicScale] using contact⟩

theorem distinct_lifted_pieceRoutes_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstCopy secondCopy : Cell) (different : (first.2,firstCopy) ≠ (second.2,secondCopy))
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (liftedPieceRoute source drawing first firstCopy) point)
    (secondContains : GridPolyline.RealContains (liftedPieceRoute source drawing second secondCopy) point) :
    (point = realCell (Cell.scale (cubicScale drawing) ((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCopy)).start) ∨
      point = realCell (Cell.scale (cubicScale drawing) ((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCopy)).finish)) ∧
    (point = realCell (Cell.scale (cubicScale drawing) ((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCopy)).start) ∨
      point = realCell (Cell.scale (cubicScale drawing) ((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCopy)).finish)) := by
  have firstParts : GridPolyline.RealContains (liftedCoreRoute source drawing first firstCopy) point ∨
      ∃ target : Bool, GridPolyline.RealContains (liftedPieceFan source drawing first target firstCopy) point := by
    rcases (liftedPieceRoute_contains source drawing first firstCopy point).mp firstContains with contains | contains | contains
    · exact Or.inr ⟨false,contains⟩
    · exact Or.inl contains
    · exact Or.inr ⟨true,contains⟩
  have secondParts : GridPolyline.RealContains (liftedCoreRoute source drawing second secondCopy) point ∨
      ∃ target : Bool, GridPolyline.RealContains (liftedPieceFan source drawing second target secondCopy) point := by
    rcases (liftedPieceRoute_contains source drawing second secondCopy point).mp secondContains with contains | contains | contains
    · exact Or.inr ⟨false,contains⟩
    · exact Or.inl contains
    · exact Or.inr ⟨true,contains⟩
  rcases firstParts with firstCore | ⟨firstTarget,firstFan⟩
  · rcases secondParts with secondCore | ⟨secondTarget,secondFan⟩
    · exact (distinct_lifted_coreRoutes_disjoint planar degree graphLocal drawingLocal firstMember secondMember firstCopy secondCopy different firstCore secondCore).elim
    · exact (distinct_lifted_coreRoutes_avoid_pieceFan planar degree graphLocal drawingLocal firstMember secondMember firstCopy secondCopy secondTarget different firstCore secondFan).elim
  · rcases secondParts with secondCore | ⟨secondTarget,secondFan⟩
    · exact (distinct_lifted_coreRoutes_avoid_pieceFan planar degree graphLocal drawingLocal secondMember firstMember secondCopy firstCopy firstTarget different.symm secondCore firstFan).elim
    · have contact := distinct_lifted_pieceFans_contact planar degree graphLocal drawingLocal firstMember secondMember
        firstTarget secondTarget firstCopy secondCopy different firstFan secondFan
      constructor
      · cases firstTarget
        · exact Or.inl contact.1
        · exact Or.inr contact.1
      · cases secondTarget
        · exact Or.inl contact.2
        · exact Or.inr contact.2

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
