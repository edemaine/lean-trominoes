/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanGeometry
import LeanTrominoes.GridSegmentRealAxisBox

/-! # Vertical anchors and vertical boundary contacts of assigned fans -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing DegreeThreeVertexNormalization

theorem AnchorProfile.vertical_anchor_y (profile : AnchorProfile) (index : Fin 4) (north : Bool)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    (group : profile.anchorGroups[index.val]? = some (if north then 3 else 1)) :
    (profile.anchors[index.val]?.getD (0,0)).2 = if north then 10 else -10 := by
  revert degree valid group
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> cases north <;> decide +kernel

theorem BendFan.vertical_boundary_certificate (profile : BendFan.Profile) (index north : Bool) (valid : profile.Valid) :
    TemplateBoxContactCertificate (profile.route index) (rectangleBoundaryRoute (if north then .north else .south))
      (profile.port index) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases index <;> cases north <;> decide +kernel

end LeanTrominoes.OrthogonalDrawingRefinement
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem fanAnchor_vertical_y {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing))
    (north : Bool) (key : (shiftedDrawing source drawing).portRayKey port = if north then .up else .down) :
    (fanAnchor source drawing port).2 = if north then 10 else -10 := by
  have childDegree := subdivisionGraph_degreeAtMost degree (by decide) drawing
  have distinct := shifted_distinctPortRayKeys planar
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) member
  cases vertex : port.vertex with
  | original value =>
      have last := incidenceTemplate_last_some distinct childDegree member
      have anchor : fanAnchor source drawing port = portBoundaryAnchor (subdivisionGraph source drawing) (shiftedDrawing source drawing) port := by
        simp only [fanAnchor,fanRoute,vertex,last,Option.getD_some]
      rw [anchor]
      apply AnchorProfile.vertical_anchor_y _ _ north (vertexAnchorProfile_degree_le_four distinct childDegree _)
        (incidenceAnchorIndex_valid distinct childDegree member)
      rw [incidenceAnchor_group distinct childDegree member,key]
      cases north <;> rfl
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      have atBend : port ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) := by
        simpa only [vertex] using port_mem_portsAt (subdivisionGraph source drawing) member
      have selected := bendPortIndex_class vertexMember atBend
      rw [key] at selected
      have boundary := BendFan.port_boundary (bendProfile source drawing edgeIndex pointIndex)
        (bendPortIndex source drawing edgeIndex pointIndex port) (bendProfile_valid planar vertexMember)
      rw [selected] at boundary
      have horizontalZero : (BendFan.rayClass (if north then StraightRayKey.up else .down)).horizontalSign = 0 := by
        cases north <;> rfl
      have y := boundary.2 horizontalZero
      cases north <;> simpa only [fanAnchor,fanRoute,vertex,BendFan.Profile.port,Bool.false_eq_true,ite_false,ite_true,
        BendFan.rayClass,BendFan.RayClass.verticalSign,mul_neg_one,mul_one] using y

theorem fanRoute_vertical_boundary_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing))
    (north : Bool) {point : ℝ × ℝ} (contains : GridPolyline.RealContains (fanRoute source drawing port) point)
    (height : point.2 = if north then 10 else -10) : point = realCell (fanAnchor source drawing port) := by
  have bounds := GridPolyline.realContains_bounds (fanRoute_bounds source drawing port) contains
  have boundaryContains : GridPolyline.RealContains (rectangleBoundaryRoute (if north then .north else .south)) point := by
    refine ⟨⟨(-5,if north then 10 else -10),(5,if north then 10 else -10)⟩,?_,
      GridSegment.realContains_of_axis_box ?_ ?_⟩
    · cases north <;> simp [rectangleBoundaryRoute,gridPolylineSegments]
    · cases north <;> simp [GridSegment.IsAxisAligned,GridSegment.IsHorizontal]
    · cases north <;> simp only [GridSegment.RealBoxContains]
      all_goals
        norm_num at height bounds ⊢
        exact ⟨bounds.1,bounds.2.1,by linarith,by linarith⟩
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) member
  cases vertex : port.vertex with
  | original value =>
      have contact := rectangleTemplate_boundary_contact
        (vertexAnchorProfile (subdivisionGraph source drawing) (shiftedDrawing source drawing) port.vertex)
        (incidenceAnchorIndex (subdivisionGraph source drawing) (shiftedDrawing source drawing) port)
        (if north then .north else .south)
        (vertexAnchorProfile_degree_le_four (shifted_distinctPortRayKeys planar)
          (subdivisionGraph_degreeAtMost degree (by decide) drawing) _)
        (incidenceAnchorIndex_valid (shifted_distinctPortRayKeys planar)
          (subdivisionGraph_degreeAtMost degree (by decide) drawing) member)
        (by simpa only [fanRoute,vertex,incidenceTemplate] using contains) boundaryContains
      simpa only [fanAnchor,fanRoute,vertex,incidenceTemplate] using contact
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      have contact := (BendFan.vertical_boundary_certificate (bendProfile source drawing edgeIndex pointIndex)
        (bendPortIndex source drawing edgeIndex pointIndex port) north (bendProfile_valid planar vertexMember)).real_contact
        (by simpa only [fanRoute,vertex] using contains) boundaryContains
      simpa only [fanAnchor,fanRoute,vertex,BendFan.Profile.port] using contact

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
