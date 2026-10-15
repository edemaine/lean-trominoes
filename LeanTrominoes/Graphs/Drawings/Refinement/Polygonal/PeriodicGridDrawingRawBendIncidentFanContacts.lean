/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendIncidentVerticalFanContacts
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedIncidentCores
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendFanContacts

/-! # Cores can touch arbitrary incident fans only at their own anchors -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem IncidentCoreData.horizontal_fan_halfPlane {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (horizontal : raw.direction.1 ≠ 0) (otherPort : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) raw.start otherPort) point) :
    (if 0 < raw.direction.1 then (1 : ℝ) else -1)*
      (point.1-(core.scale (Cubic.rasterFactor drawing.gridSize)).start.1) ≤ 0 := by
  have bounds := fanAt_real_bounds source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    raw.start otherPort fanContains
  simp only [Int.cast_natCast] at bounds
  have anchor := fanAnchor_x planar degree data.member
  by_cases right : 0 < raw.direction.1
  · rw [data.right_key right] at anchor
    simp only [BendFan.horizontalSign,mul_one] at anchor
    simp only [if_pos right,one_mul,GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
      Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat]
    have upper := (abs_le.mp bounds.1).2
    nlinarith
  · have left : raw.direction.1 < 0 := by omega
    rw [data.left_key left] at anchor
    simp only [BendFan.horizontalSign,mul_neg_one] at anchor
    simp only [if_neg right,GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
      Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg]
    have lower := (abs_le.mp bounds.1).1
    nlinarith

theorem coreRoute_incidentFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (target : Bool) (otherPort : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (incidentRawSegment source drawing tagged target).start otherPort) point) :
    point = realCell ((incidentAnchoredSegment source drawing tagged target).scale (Cubic.rasterFactor drawing.gridSize)).start := by
  have data := incidentCoreData planar degree graphLocal drawingLocal member target
  by_cases vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0
  · have orientedVertical : (incidentRawSegment source drawing tagged target).direction.1 = 0 := by
      cases target
      · exact vertical
      · simp only [incidentRawSegment,ite_true,GridSegment.direction,GridSegment.reverse]
        simp only [GridSegment.direction] at vertical
        omega
    exact data.vertical_fan_contact planar degree orientedVertical otherPort
      (coreRoute_incident_box source drawing tagged target coreContains) fanContains
  · have orientedHorizontal : (incidentRawSegment source drawing tagged target).direction.1 ≠ 0 := by
      cases target
      · exact vertical
      · simp only [incidentRawSegment,ite_true,GridSegment.direction,GridSegment.reverse]
        simp only [GridSegment.direction] at vertical
        omega
    have outside := data.horizontal_fan_halfPlane planar degree orientedHorizontal otherPort fanContains
    have core := coreContains
    simp only [coreRoute,if_neg vertical] at core
    have exterior := GridSegment.kickedDigitalRoute_exterior_contacts (coreSide_unit source drawing tagged)
      (cubicCore_horizontal_width source drawing tagged vertical) core
    cases target
    · have sourceOutside : (coreSide source drawing tagged : ℝ)*(point.1-(cubicCore source drawing tagged).start.1) ≤ 0 := by
        simpa only [incidentRawSegment,incidentAnchoredSegment,Bool.false_eq_true,ite_false,coreSide,
          Int.cast_ite,Int.cast_one,Int.cast_neg,cubicCore] using outside
      exact exterior.1 sourceOutside
    · have reversedDirection : (subdivisionSegment source drawing tagged.1).reverse.direction.1 =
          -(subdivisionSegment source drawing tagged.1).direction.1 := by
        simp only [GridSegment.direction,GridSegment.reverse]
        ring
      have targetOutside : (coreSide source drawing tagged : ℝ)*((cubicCore source drawing tagged).finish.1-point.1) ≤ 0 := by
        by_cases right : 0 < (subdivisionSegment source drawing tagged.1).direction.1
        · have notReverseRight : ¬0 < (subdivisionSegment source drawing tagged.1).reverse.direction.1 := by rw [reversedDirection]; omega
          simp only [incidentRawSegment,incidentAnchoredSegment,ite_true,if_neg notReverseRight] at outside
          change (-1 : ℝ)*(point.1-(cubicCore source drawing tagged).finish.1) ≤ 0 at outside
          simp only [coreSide,if_pos right,Int.cast_one,one_mul]
          nlinarith
        · have reverseRight : 0 < (subdivisionSegment source drawing tagged.1).reverse.direction.1 := by rw [reversedDirection]; omega
          simp only [incidentRawSegment,incidentAnchoredSegment,ite_true,if_pos reverseRight] at outside
          change (1 : ℝ)*(point.1-(cubicCore source drawing tagged).finish.1) ≤ 0 at outside
          simp only [coreSide,if_neg right,Int.cast_neg,Int.cast_one]
          nlinarith
      exact exterior.2 targetOutside

theorem coreRoute_avoids_other_incident_fan {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (target : Bool) {otherPort : GraphPort (Vertex V)}
    (otherMember : otherPort ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : (incidentPort tagged target).vertex = otherPort.vertex)
    (different : incidentPort tagged target ≠ otherPort) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    ¬GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (incidentRawSegment source drawing tagged target).start otherPort) point := by
  intro fanContains
  have contact := coreRoute_incidentFan_contact planar degree graphLocal drawingLocal member target otherPort coreContains fanContains
  have data := incidentCoreData planar degree graphLocal drawingLocal member target
  have joint : ((incidentAnchoredSegment source drawing tagged target).scale (Cubic.rasterFactor drawing.gridSize)).start =
      Cell.add (Cell.scale ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
        (incidentRawSegment source drawing tagged target).start)
      (Cell.scale (Cubic.rasterFactor drawing.gridSize) (fanAnchor source drawing (incidentPort tagged target))) := by
    simp only [GridSegment.scale,Cell.scale,data.start,Cell.add]
    apply Prod.ext <;> dsimp <;> ring
  rw [contact,joint] at fanContains
  exact fanAt_avoids_other_anchor planar degree (Cubic.coreFactor drawing.gridSize)
    (Cubic.rasterFactor_positive drawing.gridSize) (incidentRawSegment source drawing tagged target).start
    data.member otherMember sameVertex different fanContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
