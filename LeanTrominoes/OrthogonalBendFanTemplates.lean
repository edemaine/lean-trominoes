/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedTemplates
import LeanTrominoes.GridPolylineRealOpenSimple
import LeanTrominoes.GridPolylineRealBounds

/-! # Sign-preserving connectors at degree-two bends

Bends may lie on a fundamental-cell boundary. These constant-size connectors
preserve every coordinate half-plane containing both incident rays. When
both rays leave the same horizontal side, the first ray is the upper one.
All finite geometric certificates are checked by the Lean kernel.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement.BendFan
open PeriodicOrthocrossing DegreeThreeVertexNormalization

private instance orthogonalPolylineDecidable (points : List Cell) : Decidable (OrthogonalPolyline points) := by
  unfold OrthogonalPolyline
  infer_instance

inductive RayClass
  | north | eastUp | east | eastDown | south | westDown | west | westUp
  deriving DecidableEq, Repr

def RayClass.horizontalSign : RayClass → Int
  | .eastUp | .east | .eastDown => 1
  | .westUp | .west | .westDown => -1
  | .north | .south => 0

def RayClass.verticalSign : RayClass → Int
  | .north | .eastUp | .westUp => 1
  | .south | .eastDown | .westDown => -1
  | .east | .west => 0

structure Profile where
  first : RayClass
  second : RayClass
  deriving DecidableEq, Repr

def Profile.sameSide (profile : Profile) : Prop :=
  profile.first.horizontalSign = profile.second.horizontalSign ∧ profile.first.horizontalSign ≠ 0

instance (profile : Profile) : Decidable profile.sameSide := by unfold Profile.sameSide; infer_instance

def Profile.Valid (profile : Profile) : Prop :=
  if profile.sameSide then
    profile.second.verticalSign ≤ profile.first.verticalSign ∧
      ¬(profile.first.verticalSign = 0 ∧ profile.second.verticalSign = 0)
  else profile.first ≠ profile.second

instance (profile : Profile) : Decidable profile.Valid := by unfold Profile.Valid; infer_instance

def horizontalConnector (horizontal vertical : Int) (verticalFirst : Bool) : List Cell :=
  if vertical = 0 then [(0,0),(horizontal,0)]
  else if verticalFirst then [(0,0),(0,vertical),(horizontal,vertical)]
  else [(0,0),(horizontal,0),(horizontal,vertical)]

def singleConnector (ray : RayClass) : List Cell :=
  if ray.horizontalSign = 0 then [(0,0),(0,10*ray.verticalSign)]
  else horizontalConnector (5*ray.horizontalSign) (2*ray.verticalSign) false

def Profile.route (profile : Profile) (second : Bool) : List Cell :=
  if profile.sameSide then
    if profile.first.verticalSign = profile.second.verticalSign then
      if profile.first.verticalSign = 1 then
        if second then horizontalConnector (5*profile.first.horizontalSign) 2 false
        else horizontalConnector (5*profile.first.horizontalSign) 4 true
      else
        if second then horizontalConnector (5*profile.first.horizontalSign) (-4) true
        else horizontalConnector (5*profile.first.horizontalSign) (-2) false
    else
      horizontalConnector (5*profile.first.horizontalSign)
        (2*(if second then profile.second.verticalSign else profile.first.verticalSign)) true
  else singleConnector (if second then profile.second else profile.first)

def Profile.port (profile : Profile) (second : Bool) : Cell :=
  (profile.route second).getLast?.getD (0,0)

theorem route_head (profile : Profile) (second : Bool) :
    (profile.route second).head? = some (0,0) := by
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem route_last (profile : Profile) (second : Bool) :
    (profile.route second).getLast? = some (profile.port second) := by
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem route_orthogonal (profile : Profile) (second : Bool) (valid : profile.Valid) :
    OrthogonalPolyline (profile.route second) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem route_simple_certificate (profile : Profile) (second : Bool) (valid : profile.Valid) :
    GridPolyline.SimpleBoxCertificate (profile.route second) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem route_simple (profile : Profile) (second : Bool) (valid : profile.Valid) :
    GridPolyline.IsRealOpenSimple (profile.route second) :=
  GridPolyline.isRealOpenSimple_of_box_certificate (route_simple_certificate profile second valid)

theorem pair_certificate (profile : Profile) (valid : profile.Valid) :
    TemplateBoxContactCertificate (profile.route false) (profile.route true) (0,0) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> decide +kernel

theorem routes_contact (profile : Profile) (valid : profile.Valid) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (profile.route false) point)
    (secondContains : GridPolyline.RealContains (profile.route true) point) : point = realCell (0,0) :=
  (pair_certificate profile valid).real_contact firstContains secondContains

theorem route_bounds (profile : Profile) (second : Bool) :
    ∀ point ∈ profile.route second, -5 ≤ point.1 ∧ point.1 ≤ 5 ∧ -10 ≤ point.2 ∧ point.2 ≤ 10 := by
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem port_boundary (profile : Profile) (second : Bool) (valid : profile.Valid) :
    let ray := if second then profile.second else profile.first
    (profile.port second).1 = 5*ray.horizontalSign ∧
      (ray.horizontalSign = 0 → (profile.port second).2 = 10*ray.verticalSign) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem distinct_ports (profile : Profile) (valid : profile.Valid) : profile.port false ≠ profile.port true := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> decide +kernel

theorem sameSide_port_gap (profile : Profile) (valid : profile.Valid) (same : profile.sameSide) :
    (profile.port true).2+2 ≤ (profile.port false).2 := by
  revert valid same
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> decide +kernel

theorem preserves_halfPlanes (profile : Profile) (second : Bool) (valid : profile.Valid) :
    ∀ point ∈ profile.route second,
      ((0 ≤ profile.first.horizontalSign ∧ 0 ≤ profile.second.horizontalSign) → 0 ≤ point.1) ∧
      ((profile.first.horizontalSign ≤ 0 ∧ profile.second.horizontalSign ≤ 0) → point.1 ≤ 0) ∧
      ((0 ≤ profile.first.verticalSign ∧ 0 ≤ profile.second.verticalSign) → 0 ≤ point.2) ∧
      ((profile.first.verticalSign ≤ 0 ∧ profile.second.verticalSign ≤ 0) → point.2 ≤ 0) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

theorem avoids_other_port (profile : Profile) (second : Bool) (valid : profile.Valid) :
    ∀ piece ∈ gridPolylineSegments (profile.route second), ¬piece.Contains (profile.port (!second)) := by
  revert valid
  rcases profile with ⟨first,last⟩
  cases first <;> cases last <;> cases second <;> decide +kernel

end LeanTrominoes.OrthogonalDrawingRefinement.BendFan
