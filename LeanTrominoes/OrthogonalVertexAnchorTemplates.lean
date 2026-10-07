/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalVertexAnchorData
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedTemplates

/-! # Kernel-checked connectors for all degree-four rectangle anchor profiles -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing DegreeThreeVertexNormalization

def rectangleTemplateRaw : Nat → Nat → Bool → Bool → Nat → List Cell
  | 0, 0, false, true, 0 => [(0,0),(1,0),(1,-9),(0,-9),(0,-10)]
  | 0, 0, true, false, 0 => [(0,0),(1,0),(1,1),(0,1),(0,10)]
  | 0, 0, true, true, 0 => [(0,0),(0,-10)]
  | 0, 0, true, true, 1 => [(0,0),(1,0),(1,1),(0,1),(0,10)]
  | 0, 1, false, false, 0 => [(0,0),(0,1),(3,1),(3,7),(5,7)]
  | 0, 1, false, true, 0 => [(0,0),(-1,0),(-1,7),(5,7)]
  | 0, 1, false, true, 1 => [(0,0),(0,1),(2,1),(2,-6),(0,-6),(0,-10)]
  | 0, 1, true, false, 0 => [(0,0),(-1,0),(-1,7),(5,7)]
  | 0, 1, true, false, 1 => [(0,0),(0,-1),(-2,-1),(-2,9),(0,9),(0,10)]
  | 0, 1, true, true, 0 => [(0,0),(3,0),(3,7),(5,7)]
  | 0, 1, true, true, 1 => [(0,0),(0,-10)]
  | 0, 1, true, true, 2 => [(0,0),(-1,0),(-1,7),(0,7),(0,10)]
  | 0, 2, false, false, 0 => [(0,0),(-2,0),(-2,7),(5,7)]
  | 0, 2, false, false, 1 => [(0,0),(0,5),(5,5)]
  | 0, 2, false, true, 0 => [(0,0),(-1,0),(-1,4),(3,4),(3,7),(5,7)]
  | 0, 2, false, true, 1 => [(0,0),(0,1),(4,1),(4,5),(5,5)]
  | 0, 2, false, true, 2 => [(0,0),(0,-10)]
  | 0, 2, true, false, 0 => [(0,0),(2,0),(2,7),(5,7)]
  | 0, 2, true, false, 1 => [(0,0),(0,-1),(3,-1),(3,5),(5,5)]
  | 0, 2, true, false, 2 => [(0,0),(-1,0),(-1,1),(0,1),(0,10)]
  | 0, 2, true, true, 0 => [(0,0),(1,0),(1,7),(5,7)]
  | 0, 2, true, true, 1 => [(0,0),(0,-1),(3,-1),(3,5),(5,5)]
  | 0, 2, true, true, 2 => [(0,0),(-1,0),(-1,-9),(0,-9),(0,-10)]
  | 0, 2, true, true, 3 => [(0,0),(0,10)]
  | 0, 3, false, false, 0 => [(0,0),(-1,0),(-1,7),(5,7)]
  | 0, 3, false, false, 1 => [(0,0),(0,5),(5,5)]
  | 0, 3, false, false, 2 => [(0,0),(1,0),(1,2),(4,2),(4,3),(5,3)]
  | 0, 3, false, true, 0 => [(0,0),(0,7),(5,7)]
  | 0, 3, false, true, 1 => [(0,0),(1,0),(1,5),(5,5)]
  | 0, 3, false, true, 2 => [(0,0),(0,-1),(2,-1),(2,3),(5,3)]
  | 0, 3, false, true, 3 => [(0,0),(-1,0),(-1,-9),(0,-9),(0,-10)]
  | 0, 3, true, false, 0 => [(0,0),(0,7),(5,7)]
  | 0, 3, true, false, 1 => [(0,0),(1,0),(1,5),(5,5)]
  | 0, 3, true, false, 2 => [(0,0),(0,-1),(2,-1),(2,3),(5,3)]
  | 0, 3, true, false, 3 => [(0,0),(-2,0),(-2,9),(0,9),(0,10)]
  | 0, 4, false, false, 0 => [(0,0),(-1,0),(-1,6),(2,6),(2,7),(5,7)]
  | 0, 4, false, false, 1 => [(0,0),(0,5),(5,5)]
  | 0, 4, false, false, 2 => [(0,0),(2,0),(2,3),(5,3)]
  | 0, 4, false, false, 3 => [(0,0),(0,-1),(4,-1),(4,1),(5,1)]
  | 1, 0, false, false, 0 => [(0,0),(0,-7),(-5,-7)]
  | 1, 0, false, true, 0 => [(0,0),(1,0),(1,-1),(0,-1),(0,-10)]
  | 1, 0, false, true, 1 => [(0,0),(0,1),(-3,1),(-3,-7),(-5,-7)]
  | 1, 0, true, false, 0 => [(0,0),(0,-7),(-5,-7)]
  | 1, 0, true, false, 1 => [(0,0),(1,0),(1,2),(0,2),(0,10)]
  | 1, 0, true, true, 0 => [(0,0),(1,0),(1,-8),(0,-8),(0,-10)]
  | 1, 0, true, true, 1 => [(0,0),(0,-1),(-3,-1),(-3,-7),(-5,-7)]
  | 1, 0, true, true, 2 => [(0,0),(0,10)]
  | 1, 1, false, false, 0 => [(0,0),(3,0),(3,7),(5,7)]
  | 1, 1, false, false, 1 => [(0,0),(-1,0),(-1,-4),(-4,-4),(-4,-7),(-5,-7)]
  | 1, 1, false, true, 0 => [(0,0),(0,7),(5,7)]
  | 1, 1, false, true, 1 => [(0,0),(2,0),(2,-8),(0,-8),(0,-10)]
  | 1, 1, false, true, 2 => [(0,0),(-3,0),(-3,-7),(-5,-7)]
  | 1, 1, true, false, 0 => [(0,0),(0,7),(5,7)]
  | 1, 1, true, false, 1 => [(0,0),(1,0),(1,-7),(-5,-7)]
  | 1, 1, true, false, 2 => [(0,0),(0,-1),(-1,-1),(-1,9),(0,9),(0,10)]
  | 1, 1, true, true, 0 => [(0,0),(4,0),(4,7),(5,7)]
  | 1, 1, true, true, 1 => [(0,0),(0,-10)]
  | 1, 1, true, true, 2 => [(0,0),(-4,0),(-4,-7),(-5,-7)]
  | 1, 1, true, true, 3 => [(0,0),(0,10)]
  | 1, 2, false, false, 0 => [(0,0),(-1,0),(-1,7),(5,7)]
  | 1, 2, false, false, 1 => [(0,0),(0,2),(4,2),(4,5),(5,5)]
  | 1, 2, false, false, 2 => [(0,0),(1,0),(1,-7),(-5,-7)]
  | 1, 2, false, true, 0 => [(0,0),(-1,0),(-1,7),(5,7)]
  | 1, 2, false, true, 1 => [(0,0),(0,5),(5,5)]
  | 1, 2, false, true, 2 => [(0,0),(1,0),(1,-6),(0,-6),(0,-10)]
  | 1, 2, false, true, 3 => [(0,0),(0,-1),(-4,-1),(-4,-7),(-5,-7)]
  | 1, 2, true, false, 0 => [(0,0),(3,0),(3,7),(5,7)]
  | 1, 2, true, false, 1 => [(0,0),(0,-1),(4,-1),(4,5),(5,5)]
  | 1, 2, true, false, 2 => [(0,0),(-1,0),(-1,-7),(-5,-7)]
  | 1, 2, true, false, 3 => [(0,0),(0,10)]
  | 1, 3, false, false, 0 => [(0,0),(0,7),(5,7)]
  | 1, 3, false, false, 1 => [(0,0),(1,0),(1,5),(5,5)]
  | 1, 3, false, false, 2 => [(0,0),(0,-1),(2,-1),(2,3),(5,3)]
  | 1, 3, false, false, 3 => [(0,0),(-1,0),(-1,-7),(-5,-7)]
  | 2, 0, false, false, 0 => [(0,0),(0,-3),(-3,-3),(-3,-7),(-5,-7)]
  | 2, 0, false, false, 1 => [(0,0),(0,1),(-4,1),(-4,-5),(-5,-5)]
  | 2, 0, false, true, 0 => [(0,0),(0,-10)]
  | 2, 0, false, true, 1 => [(0,0),(-2,0),(-2,-7),(-5,-7)]
  | 2, 0, false, true, 2 => [(0,0),(1,0),(1,1),(-4,1),(-4,-5),(-5,-5)]
  | 2, 0, true, false, 0 => [(0,0),(1,0),(1,-7),(-5,-7)]
  | 2, 0, true, false, 1 => [(0,0),(0,-5),(-5,-5)]
  | 2, 0, true, false, 2 => [(0,0),(-1,0),(-1,4),(0,4),(0,10)]
  | 2, 0, true, true, 0 => [(0,0),(0,-10)]
  | 2, 0, true, true, 1 => [(0,0),(-3,0),(-3,-7),(-5,-7)]
  | 2, 0, true, true, 2 => [(0,0),(0,1),(-4,1),(-4,-5),(-5,-5)]
  | 2, 0, true, true, 3 => [(0,0),(1,0),(1,3),(0,3),(0,10)]
  | 2, 1, false, false, 0 => [(0,0),(-1,0),(-1,7),(5,7)]
  | 2, 1, false, false, 1 => [(0,0),(0,1),(3,1),(3,-7),(-5,-7)]
  | 2, 1, false, false, 2 => [(0,0),(0,-3),(-2,-3),(-2,-5),(-5,-5)]
  | 2, 1, false, true, 0 => [(0,0),(4,0),(4,7),(5,7)]
  | 2, 1, false, true, 1 => [(0,0),(0,-10)]
  | 2, 1, false, true, 2 => [(0,0),(-1,0),(-1,-7),(-5,-7)]
  | 2, 1, false, true, 3 => [(0,0),(0,1),(-3,1),(-3,-2),(-4,-2),(-4,-5),(-5,-5)]
  | 2, 1, true, false, 0 => [(0,0),(4,0),(4,7),(5,7)]
  | 2, 1, true, false, 1 => [(0,0),(0,-7),(-5,-7)]
  | 2, 1, true, false, 2 => [(0,0),(-2,0),(-2,-5),(-5,-5)]
  | 2, 1, true, false, 3 => [(0,0),(0,10)]
  | 2, 2, false, false, 0 => [(0,0),(0,7),(5,7)]
  | 2, 2, false, false, 1 => [(0,0),(2,0),(2,5),(5,5)]
  | 2, 2, false, false, 2 => [(0,0),(0,-7),(-5,-7)]
  | 2, 2, false, false, 3 => [(0,0),(-2,0),(-2,-5),(-5,-5)]
  | 3, 0, false, false, 0 => [(0,0),(1,0),(1,-7),(-5,-7)]
  | 3, 0, false, false, 1 => [(0,0),(0,-3),(-2,-3),(-2,-5),(-5,-5)]
  | 3, 0, false, false, 2 => [(0,0),(-3,0),(-3,-3),(-5,-3)]
  | 3, 0, false, true, 0 => [(0,0),(1,0),(1,-8),(0,-8),(0,-10)]
  | 3, 0, false, true, 1 => [(0,0),(0,-7),(-5,-7)]
  | 3, 0, false, true, 2 => [(0,0),(-3,0),(-3,-5),(-5,-5)]
  | 3, 0, false, true, 3 => [(0,0),(0,1),(-4,1),(-4,-3),(-5,-3)]
  | 3, 0, true, false, 0 => [(0,0),(1,0),(1,-2),(-1,-2),(-1,-7),(-5,-7)]
  | 3, 0, true, false, 1 => [(0,0),(0,-1),(-2,-1),(-2,-5),(-5,-5)]
  | 3, 0, true, false, 2 => [(0,0),(-3,0),(-3,-3),(-5,-3)]
  | 3, 0, true, false, 3 => [(0,0),(0,10)]
  | 3, 1, false, false, 0 => [(0,0),(1,0),(1,7),(5,7)]
  | 3, 1, false, false, 1 => [(0,0),(0,-7),(-5,-7)]
  | 3, 1, false, false, 2 => [(0,0),(-3,0),(-3,-5),(-5,-5)]
  | 3, 1, false, false, 3 => [(0,0),(0,1),(-4,1),(-4,-3),(-5,-3)]
  | 4, 0, false, false, 0 => [(0,0),(1,0),(1,-7),(-5,-7)]
  | 4, 0, false, false, 1 => [(0,0),(0,-1),(-1,-1),(-1,-5),(-5,-5)]
  | 4, 0, false, false, 2 => [(0,0),(-3,0),(-3,-3),(-5,-3)]
  | 4, 0, false, false, 3 => [(0,0),(0,1),(-4,1),(-4,-1),(-5,-1)]
  | _, _, _, _, _ => [(0,0),(1,0)]

def rectangleTemplate (profile : AnchorProfile) (index : Fin 4) : List Cell :=
  rectangleTemplateRaw profile.leftCount.val profile.rightCount.val profile.top profile.bottom index.val

theorem rectangleTemplate_simple_certificate (profile : AnchorProfile) (index : Fin 4) :
    GridPolyline.SimpleBoxCertificate (rectangleTemplate profile index) := by
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem rectangleTemplate_orthogonal (profile : AnchorProfile) (index : Fin 4) :
    OrthogonalPolyline (rectangleTemplate profile index) := by
  unfold OrthogonalPolyline GridSegment.IsAxisAligned GridSegment.IsHorizontal GridSegment.IsVertical
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem rectangleTemplate_head (profile : AnchorProfile) (index : Fin 4) :
    (rectangleTemplate profile index).head? = some (0,0) := by
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem rectangleTemplate_last (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree) :
    (rectangleTemplate profile index).getLast? = profile.anchors[index.val]? := by
  revert degree valid
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem rectangleTemplate_points_in_rectangle (profile : AnchorProfile) (index : Fin 4) :
    ∀ point ∈ rectangleTemplate profile index,
      -5 ≤ point.1 ∧ point.1 ≤ 5 ∧ -10 ≤ point.2 ∧ point.2 ≤ 10 := by
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem rectangleTemplate_isRealOpenSimple (profile : AnchorProfile) (index : Fin 4) :
    GridPolyline.IsRealOpenSimple (rectangleTemplate profile index) :=
  GridPolyline.isRealOpenSimple_of_box_certificate (rectangleTemplate_simple_certificate profile index)

end LeanTrominoes.OrthogonalDrawingRefinement
