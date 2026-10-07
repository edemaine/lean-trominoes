/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedPort
import LeanTrominoes.GridPolylineRealOpenSimple
import LeanTrominoes.GridPolylineRealBounds

/-! # Uncolored degree-three templates with a selected west incidence -/
namespace LeanTrominoes.DegreeThreeVertexNormalization

def selectedTemplate : VertexSide → VertexSide → CanonicalVertexPort → List Cell
  | .east, .east, .west => [(0,0),(-1,0),(-1,-1),(-7,-1),(-7,0),(-8,0)]
  | .east, .east, .north => [(0,0),(0,8)]
  | .east, .east, .east => [(0,0),(1,0),(1,-7),(0,-7),(0,-8)]
  | .east, .north, .west => [(0,0),(-1,0),(-1,-1),(3,-1),(3,4),(1,4),(1,6),(0,6),(0,8)]
  | .east, .north, .north => [(0,0),(0,1),(-2,1),(-2,-7),(0,-7),(0,-8)]
  | .east, .north, .east => [(0,0),(1,0),(1,2),(-3,2),(-3,1),(-5,1),(-5,0),(-8,0)]
  | .east, .west, .west => [(0,0),(-8,0)]
  | .east, .west, .north => [(0,0),(0,8)]
  | .east, .west, .east => [(0,0),(1,0),(1,-7),(0,-7),(0,-8)]
  | .east, .south, .west => [(0,0),(-1,0),(-1,-6),(0,-6),(0,-8)]
  | .east, .south, .north => [(0,0),(0,1),(-5,1),(-5,0),(-8,0)]
  | .east, .south, .east => [(0,0),(1,0),(1,5),(0,5),(0,8)]
  | .north, .east, .west => [(0,0),(-1,0),(-1,2),(3,2),(3,0),(8,0)]
  | .north, .east, .north => [(0,0),(0,1),(2,1),(2,-7),(0,-7),(0,-8)]
  | .north, .east, .east => [(0,0),(1,0),(1,-1),(-3,-1),(-3,0),(-8,0)]
  | .north, .north, .west => [(0,0),(-1,0),(-1,-6),(0,-6),(0,-8)]
  | .north, .north, .north => [(0,0),(0,1),(-2,1),(-2,0),(-8,0)]
  | .north, .north, .east => [(0,0),(8,0)]
  | .north, .west, .west => [(0,0),(-1,0),(-1,-1),(-2,-1),(-2,-2),(-7,-2),(-7,0),(-8,0)]
  | .north, .west, .north => [(0,0),(0,1),(3,1),(3,0),(8,0)]
  | .north, .west, .east => [(0,0),(1,0),(1,-6),(0,-6),(0,-8)]
  | .north, .south, .west => [(0,0),(-1,0),(-1,-1),(0,-1),(0,-8)]
  | .north, .south, .north => [(0,0),(0,1),(-6,1),(-6,0),(-8,0)]
  | .north, .south, .east => [(0,0),(8,0)]
  | .west, .east, .west => [(0,0),(-1,0),(-1,-1),(6,-1),(6,0),(8,0)]
  | .west, .east, .north => [(0,0),(0,1),(-2,1),(-2,-6),(-1,-6),(-1,-7),(0,-7),(0,-8)]
  | .west, .east, .east => [(0,0),(1,0),(1,2),(0,2),(0,8)]
  | .west, .north, .west => [(0,0),(-1,0),(-1,3),(0,3),(0,8)]
  | .west, .north, .north => [(0,0),(0,1),(5,1),(5,0),(8,0)]
  | .west, .north, .east => [(0,0),(1,0),(1,-1),(0,-1),(0,-8)]
  | .west, .west, .west => [(0,0),(-1,0),(-1,-1),(0,-1),(0,-8)]
  | .west, .west, .north => [(0,0),(0,8)]
  | .west, .west, .east => [(0,0),(8,0)]
  | .west, .south, .west => [(0,0),(-1,0),(-1,-7),(0,-7),(0,-8)]
  | .west, .south, .north => [(0,0),(0,8)]
  | .west, .south, .east => [(0,0),(8,0)]
  | .south, .east, .west => [(0,0),(-1,0),(-1,-1),(2,-1),(2,0),(8,0)]
  | .south, .east, .north => [(0,0),(0,1),(-5,1),(-5,0),(-8,0)]
  | .south, .east, .east => [(0,0),(1,0),(1,7),(0,7),(0,8)]
  | .south, .north, .west => [(0,0),(-1,0),(-1,6),(0,6),(0,8)]
  | .south, .north, .north => [(0,0),(0,1),(7,1),(7,0),(8,0)]
  | .south, .north, .east => [(0,0),(1,0),(1,-1),(-7,-1),(-7,0),(-8,0)]
  | .south, .west, .west => [(0,0),(-8,0)]
  | .south, .west, .north => [(0,0),(0,8)]
  | .south, .west, .east => [(0,0),(2,0),(2,1),(7,1),(7,0),(8,0)]
  | .south, .south, .west => [(0,0),(-1,0),(-1,1),(-7,1),(-7,0),(-8,0)]
  | .south, .south, .north => [(0,0),(0,8)]
  | .south, .south, .east => [(0,0),(1,0),(1,-1),(5,-1),(5,0),(8,0)]

def selectedBoundaryPoint (omitted selected : VertexSide) (port : CanonicalVertexPort) : Cell :=
  Cell.scale 8 (selectedBoundarySide omitted selected port).direction.step

def TemplateBoxContactCertificate (first second : List Cell) (joint : Cell) : Prop :=
  ∀ a ∈ gridPolylineSegments first, ∀ b ∈ gridPolylineSegments second,
    (max (min a.start.1 a.finish.1) (min b.start.1 b.finish.1) ≤
        min (max a.start.1 a.finish.1) (max b.start.1 b.finish.1) ∧
      max (min a.start.2 a.finish.2) (min b.start.2 b.finish.2) ≤
        min (max a.start.2 a.finish.2) (max b.start.2 b.finish.2)) →
      GridSegment.BoxIntersectionIsPoint a b joint

instance (first second : List Cell) (joint : Cell) :
    Decidable (TemplateBoxContactCertificate first second joint) := by
  unfold TemplateBoxContactCertificate
  infer_instance

theorem selectedTemplate_endpoints (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    (selectedTemplate omitted selected port).head? = some (0,0) ∧
      (selectedTemplate omitted selected port).getLast? = some (selectedBoundaryPoint omitted selected port) := by
  cases omitted <;> cases selected <;> cases port <;> decide +kernel

theorem selectedTemplate_firstDirection (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    AxisDirection.polylineFirstDirection (selectedTemplate omitted selected port) = port.direction := by
  cases omitted <;> cases selected <;> cases port <;> decide +kernel

theorem selectedTemplate_orthogonal (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    PeriodicOrthocrossing.OrthogonalPolyline (selectedTemplate omitted selected port) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline GridSegment.IsAxisAligned GridSegment.IsHorizontal GridSegment.IsVertical
  cases omitted <;> cases selected <;> cases port <;> decide +kernel

theorem selectedTemplate_simple_certificate (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    GridPolyline.SimpleBoxCertificate (selectedTemplate omitted selected port) := by
  cases omitted <;> cases selected <;> cases port <;> decide +kernel

theorem selectedTemplate_points_in_square (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    ∀ point ∈ selectedTemplate omitted selected port,
      -8 ≤ point.1 ∧ point.1 ≤ 8 ∧ -8 ≤ point.2 ∧ point.2 ≤ 8 := by
  cases omitted <;> cases selected <;> cases port <;> decide +kernel

theorem selectedTemplate_pair_certificate (omitted selected : VertexSide) (first second : CanonicalVertexPort)
    (different : first ≠ second) :
    TemplateBoxContactCertificate (selectedTemplate omitted selected first) (selectedTemplate omitted selected second) (0,0) := by
  revert different
  cases omitted <;> cases selected <;> cases first <;> cases second <;> decide +kernel

theorem TemplateBoxContactCertificate.real_contact {first second : List Cell} {joint : Cell}
    (certificate : TemplateBoxContactCertificate first second joint) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains first point) (secondContains : GridPolyline.RealContains second point) :
    point = realCell joint := by
  obtain ⟨a,am,ah⟩ := firstContains
  obtain ⟨b,bm,bh⟩ := secondContains
  exact GridSegment.real_intersection_eq_of_box_certificate
    (certificate a am b bm (GridSegment.real_boxes_overlap_of_real_contacts ah bh)) ah bh

theorem selectedTemplate_isRealOpenSimple (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    GridPolyline.IsRealOpenSimple (selectedTemplate omitted selected port) :=
  GridPolyline.isRealOpenSimple_of_box_certificate (selectedTemplate_simple_certificate omitted selected port)

theorem selectedTemplate_real_contacts_center (omitted selected : VertexSide) (first second : CanonicalVertexPort)
    (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (selectedTemplate omitted selected first) point)
    (secondContains : GridPolyline.RealContains (selectedTemplate omitted selected second) point) :
    point = realCell (0,0) :=
  (selectedTemplate_pair_certificate omitted selected first second different).real_contact firstContains secondContains

def squareBoundaryRoute : VertexSide → List Cell
  | .east => [(8,-8),(8,8)]
  | .north => [(-8,8),(8,8)]
  | .west => [(-8,-8),(-8,8)]
  | .south => [(-8,-8),(8,-8)]

theorem selectedTemplate_boundary_certificate (omitted selected : VertexSide) (port : CanonicalVertexPort)
    (side : VertexSide) :
    TemplateBoxContactCertificate (selectedTemplate omitted selected port) (squareBoundaryRoute side)
      (selectedBoundaryPoint omitted selected port) := by
  cases omitted <;> cases selected <;> cases port <;> cases side <;> decide +kernel

theorem selectedTemplate_real_boundary_contact (omitted selected : VertexSide) (port : CanonicalVertexPort)
    (side : VertexSide) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (selectedTemplate omitted selected port) point)
    (boundary : GridPolyline.RealContains (squareBoundaryRoute side) point) :
    point = realCell (selectedBoundaryPoint omitted selected port) :=
  (selectedTemplate_boundary_certificate omitted selected port side).real_contact contains boundary

end LeanTrominoes.DegreeThreeVertexNormalization
