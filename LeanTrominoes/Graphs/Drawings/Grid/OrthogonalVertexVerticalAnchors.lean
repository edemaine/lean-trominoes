/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorGroups

/-! # The unique up and down incidences use the top and bottom anchors -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem AnchorProfile.down_anchor (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    (down : profile.anchorGroups[index.val]? = some 1) :
    profile.anchors[index.val]?.getD (0,0) = (0,-10) := by
  revert degree valid down
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem AnchorProfile.up_anchor (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    (up : profile.anchorGroups[index.val]? = some 3) :
    profile.anchors[index.val]?.getD (0,0) = (0,10) := by
  revert degree valid up
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

end LeanTrominoes.OrthogonalDrawingRefinement
