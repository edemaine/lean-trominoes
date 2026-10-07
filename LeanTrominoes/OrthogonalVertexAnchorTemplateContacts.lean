/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalVertexAnchorTemplates

/-! # Rectangle connectors meet only at the center and their own boundary anchors -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing DegreeThreeVertexNormalization

theorem rectangleTemplate_pair_certificate (profile : AnchorProfile) (first second : Fin 4)
    (degree : profile.degree ≤ 4) (firstValid : first.val < profile.degree) (secondValid : second.val < profile.degree)
    (different : first ≠ second) :
    TemplateBoxContactCertificate (rectangleTemplate profile first) (rectangleTemplate profile second) (0,0) := by
  revert degree firstValid secondValid different
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;>
    fin_cases first <;> fin_cases second <;> decide +kernel

def rectangleBoundaryRoute : VertexSide → List Cell
  | .east => [(5,-10),(5,10)]
  | .north => [(-5,10),(5,10)]
  | .west => [(-5,-10),(-5,10)]
  | .south => [(-5,-10),(5,-10)]

theorem rectangleTemplate_boundary_certificate (profile : AnchorProfile) (index : Fin 4) (side : VertexSide)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree) :
    TemplateBoxContactCertificate (rectangleTemplate profile index) (rectangleBoundaryRoute side)
      ((rectangleTemplate profile index).getLast?.getD (0,0)) := by
  revert degree valid
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;>
    fin_cases index <;> cases side <;> decide +kernel

theorem rectangleTemplate_contacts_center (profile : AnchorProfile) (first second : Fin 4)
    (degree : profile.degree ≤ 4) (firstValid : first.val < profile.degree) (secondValid : second.val < profile.degree)
    (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (rectangleTemplate profile first) point)
    (secondContains : GridPolyline.RealContains (rectangleTemplate profile second) point) : point = realCell (0,0) :=
  (rectangleTemplate_pair_certificate profile first second degree firstValid secondValid different).real_contact firstContains secondContains

theorem rectangleTemplate_boundary_contact (profile : AnchorProfile) (index : Fin 4) (side : VertexSide)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (rectangleTemplate profile index) point)
    (boundary : GridPolyline.RealContains (rectangleBoundaryRoute side) point) :
    point = realCell ((rectangleTemplate profile index).getLast?.getD (0,0)) :=
  (rectangleTemplate_boundary_certificate profile index side degree valid).real_contact contains boundary

end LeanTrominoes.OrthogonalDrawingRefinement
