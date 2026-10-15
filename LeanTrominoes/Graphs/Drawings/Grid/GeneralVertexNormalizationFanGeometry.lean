/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationDistinctPortSides
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity

/-! # Geometry of the assigned uncolored vertex fans -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing DegreeThreeVertexNormalization

theorem straightTemplate_orthogonal (side : VertexSide) : OrthogonalPolyline (straightTemplate side) := by
  unfold OrthogonalPolyline GridSegment.IsAxisAligned GridSegment.IsHorizontal GridSegment.IsVertical
  cases side <;> decide +kernel

theorem straightTemplate_pair_certificate (first second : VertexSide) (different : first ≠ second) :
    TemplateBoxContactCertificate (straightTemplate first) (straightTemplate second) (0,0) := by
  revert different
  cases first <;> cases second <;> decide +kernel

theorem straightTemplate_boundary_certificate (first second : VertexSide) :
    TemplateBoxContactCertificate (straightTemplate first) (squareBoundaryRoute second)
      (Cell.scale 8 first.direction.step) := by
  cases first <;> cases second <;> decide +kernel

theorem fanAssignment_orthogonal {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) :
    OrthogonalPolyline (fanAssignment graph drawing chosen port) := by
  unfold fanAssignment
  split
  · exact selectedTemplate_orthogonal _ _ _
  · exact straightTemplate_orthogonal _

theorem fanAssignment_reverse_simple {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) :
    GridPolyline.IsRealOpenSimple (fanAssignment graph drawing chosen port).reverse := by
  apply GridPolyline.isRealOpenSimple_of_box_certificate
  unfold fanAssignment
  split
  · generalize omittedAt graph drawing port.vertex = omitted
    generalize portSide drawing (chosen port.vertex) = selected
    generalize selectedCanonicalPort omitted selected (portSide drawing port) = canonical
    cases omitted <;> cases selected <;> cases canonical <;> decide +kernel
  · generalize portSide drawing port = side
    cases side <;> decide +kernel

theorem fanAssignment_points_in_square {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) :
    ∀ point ∈ fanAssignment graph drawing chosen port,
      -8 ≤ point.1 ∧ point.1 ≤ 8 ∧ -8 ≤ point.2 ∧ point.2 ≤ 8 := by
  unfold fanAssignment
  split
  · exact selectedTemplate_points_in_square _ _ _
  · generalize portSide drawing port = side
    cases side <;> decide +kernel

theorem fanAssignment_pair_certificate {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {first second : GraphPort Vertex} (fm : first ∈ allPorts graph) (sm : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) (different : first ≠ second) :
    TemplateBoxContactCertificate (fanAssignment graph drawing chosen first)
      (fanAssignment graph drawing chosen second) (0,0) := by
  have differentSides : portSide drawing first ≠ portSide drawing second :=
    fun equal => different (distinct first fm second sm sameVertex equal)
  unfold fanAssignment
  simp only [← sameVertex]
  split
  · rename_i degree
    apply selectedTemplate_pair_certificate
    intro equal
    apply differentSides
    exact selectedCanonicalPort_injective_on_used _ _
      (portSide_ne_omittedAt distinct fm degree)
      (by simpa only [sameVertex] using portSide_ne_omittedAt distinct sm (by simpa only [sameVertex] using degree)) equal
  · exact straightTemplate_pair_certificate _ _ differentSides

theorem fanAssignment_boundary_certificate {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (side : VertexSide) :
    TemplateBoxContactCertificate (fanAssignment graph drawing chosen port) (squareBoundaryRoute side)
      (Cell.scale 8 (portSide drawing port).direction.step) := by
  unfold fanAssignment
  split
  · rename_i degree
    have boundary := selectedTemplate_boundary_certificate (omittedAt graph drawing port.vertex)
      (portSide drawing (chosen port.vertex))
      (selectedCanonicalPort (omittedAt graph drawing port.vertex) (portSide drawing (chosen port.vertex)) (portSide drawing port)) side
    simpa only [selectedBoundaryPoint,selectedBoundarySide_selectedCanonicalPort _ _ _
      (portSide_ne_omittedAt distinct member degree)] using boundary
  · exact straightTemplate_boundary_certificate _ _

def fanAt {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) (position : Cell) : List Cell :=
  translatePolyline (Cell.scale 32 position) (fanAssignment graph drawing chosen port)

theorem fanAt_real_bounds {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) (position : Cell)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (fanAt graph drawing chosen port position) point) :
    (-8 : ℝ)+32*position.1 ≤ point.1 ∧ point.1 ≤ (8 : ℝ)+32*position.1 ∧
      (-8 : ℝ)+32*position.2 ≤ point.2 ∧ point.2 ≤ (8 : ℝ)+32*position.2 := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have bounds := GridPolyline.realContains_bounds (fanAssignment_points_in_square graph drawing chosen port) original
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul,Int.cast_ofNat] at bounds
  norm_num only [Int.cast_neg,Int.cast_ofNat] at bounds
  constructor
  · linarith [bounds.1]
  constructor
  · linarith [bounds.2.1]
  constructor <;> linarith [bounds.2.2.1,bounds.2.2.2]

theorem fanAt_contacts_same_position {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (first second : GraphPort Vertex)
    {firstPosition secondPosition : Cell} {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fanAt graph drawing chosen first firstPosition) point)
    (secondContains : GridPolyline.RealContains (fanAt graph drawing chosen second secondPosition) point) :
    firstPosition = secondPosition := by
  have fb := fanAt_real_bounds _ _ _ _ _ firstContains
  have sb := fanAt_real_bounds _ _ _ _ _ secondContains
  apply Prod.ext
  · exact GridSegment.closed_interval_periodic_shifts_unique (period := 32) (lower := -8) (upper := 8)
      (point := point.1) (by norm_num) (by norm_num)
      (by simpa using And.intro fb.1 fb.2.1) (by simpa using And.intro sb.1 sb.2.1)
  · exact GridSegment.closed_interval_periodic_shifts_unique (period := 32) (lower := -8) (upper := 8)
      (point := point.2) (by norm_num) (by norm_num)
      (by simpa using And.intro fb.2.2.1 fb.2.2.2) (by simpa using And.intro sb.2.2.1 sb.2.2.2)

theorem fanAt_contacts_center {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {first second : GraphPort Vertex} (fm : first ∈ allPorts graph) (sm : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) (different : first ≠ second) (position : Cell) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fanAt graph drawing chosen first position) point)
    (secondContains : GridPolyline.RealContains (fanAt graph drawing chosen second position) point) :
    point = realCell (Cell.scale 32 position) := by
  have contact := (fanAssignment_pair_certificate distinct chosen fm sm sameVertex different).real_contact
    ((GridPolyline.realContains_translate_inverse _ _ _).mp firstContains)
    ((GridPolyline.realContains_translate_inverse _ _ _).mp secondContains)
  have hx := congrArg Prod.fst contact
  have hy := congrArg Prod.snd contact
  apply Prod.ext <;> simp only [realCell,Prod.fst,Prod.snd,Int.cast_zero] at hx hy ⊢ <;> linarith

theorem fanAt_trimmedRoute_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) {route : List Cell}
    (simple : GridPolyline.IsRealSimple route) (orthogonal : OrthogonalPolyline route) (position : Cell)
    (vertexAvoidance : GridPolyline.RealContains route (realCell position) → GridPolyline.RealIsEndpoint route (realCell position))
    {point : ℝ × ℝ} (fanContains : GridPolyline.RealContains (fanAt graph drawing chosen port position) point)
    (middleContains : GridPolyline.RealContains (GridPolyline.clippedScaledRoute route) point) :
    point = realCell (Cell.add (Cell.scale 32 position) (Cell.scale 8 (portSide drawing port).direction.step)) ∧
      GridPolyline.RealIsEndpoint (GridPolyline.clippedScaledRoute route) point := by
  have bounds := fanAt_real_bounds _ _ _ _ _ fanContains
  have contact := GridPolyline.clippedScaledRoute_neighborhood_contact simple orthogonal vertexAvoidance
    (by refine ⟨?_,?_,?_,?_⟩ <;> linarith [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]) middleContains
  obtain ⟨side,midpoint⟩ := contact.2
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  have localPoint : (point.1-(Cell.scale 32 position).1,point.2-(Cell.scale 32 position).2) =
      realCell (Cell.scale 8 side.direction.step) := by
    rw [midpoint]
    simp [realCell,Cell.add]
  rw [localPoint] at original
  have boundary := (fanAssignment_boundary_certificate distinct chosen member side).real_contact original
    (squareBoundaryRoute_contains_midpoint side)
  have cellEq := realCell_injective boundary
  exact ⟨by simpa only [cellEq] using midpoint,contact.1⟩

end LeanTrominoes.GeneralVertexNormalization
