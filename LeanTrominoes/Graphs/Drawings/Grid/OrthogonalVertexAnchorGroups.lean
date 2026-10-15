/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorData
import Mathlib.Data.List.Sort

/-! # Boundary-side order and ordinate order of rectangle anchors -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def AnchorProfile.anchorGroups (profile : AnchorProfile) : List (Fin 4) :=
  List.replicate profile.rightCount.val 0 ++ (if profile.bottom then [1] else []) ++
    List.replicate profile.leftCount.val 2 ++ (if profile.top then [3] else [])

def anchorProfileOfGroups (groups : List (Fin 4)) : AnchorProfile where
  leftCount := ⟨min (groups.countP (fun group => decide (group = 2))) 4,by omega⟩
  rightCount := ⟨min (groups.countP (fun group => decide (group = 0))) 4,by omega⟩
  top := decide (3 ∈ groups)
  bottom := decide (1 ∈ groups)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 5000 in
theorem sorted_groups_eq_anchorGroups {groups : List (Fin 4)} (bound : groups.length ≤ 4)
    (ordered : groups.Pairwise (· ≤ ·))
    (downCount : groups.countP (fun group => decide (group = 1)) ≤ 1)
    (upCount : groups.countP (fun group => decide (group = 3)) ≤ 1) :
    (anchorProfileOfGroups groups).anchorGroups = groups := by
  cases groups with
  | nil =>
    decide +kernel
  | cons a groups =>
    cases groups with
    | nil =>
      revert ordered downCount upCount
      revert a
      decide +kernel
    | cons b groups =>
      cases groups with
      | nil =>
        revert ordered downCount upCount
        revert a b
        decide +kernel
      | cons c groups =>
        cases groups with
        | nil =>
          revert ordered downCount upCount
          revert a b c
          decide +kernel
        | cons d groups =>
          cases groups with
          | nil =>
            revert ordered downCount upCount
            revert a b c d
            decide +kernel
          | cons e groups =>
            simp only [List.length_cons] at bound
            omega

def groupBoundaryX (group : Fin 4) : Int :=
  match group.val with
  | 0 => 5
  | 2 => -5
  | _ => 0

theorem AnchorProfile.anchor_x_matches_group (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree) :
    (profile.anchors[index.val]?.getD (0,0)).1 =
      groupBoundaryX (profile.anchorGroups[index.val]?.getD 0) := by
  revert degree valid
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem AnchorProfile.right_anchor_ordinates (profile : AnchorProfile) (first second : Fin 4)
    (degree : profile.degree ≤ 4) (firstValid : first.val < profile.degree) (secondValid : second.val < profile.degree)
    (ordered : first.val < second.val) (firstRight : profile.anchorGroups[first.val]? = some 0)
    (secondRight : profile.anchorGroups[second.val]? = some 0) :
    (profile.anchors[second.val]?.getD (0,0)).2 < (profile.anchors[first.val]?.getD (0,0)).2 := by
  revert degree firstValid secondValid ordered firstRight secondRight
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;>
    fin_cases first <;> fin_cases second <;> decide +kernel

theorem AnchorProfile.left_anchor_ordinates (profile : AnchorProfile) (first second : Fin 4)
    (degree : profile.degree ≤ 4) (firstValid : first.val < profile.degree) (secondValid : second.val < profile.degree)
    (ordered : first.val < second.val) (firstLeft : profile.anchorGroups[first.val]? = some 2)
    (secondLeft : profile.anchorGroups[second.val]? = some 2) :
    (profile.anchors[first.val]?.getD (0,0)).2 < (profile.anchors[second.val]?.getD (0,0)).2 := by
  revert degree firstValid secondValid ordered firstLeft secondLeft
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;>
    fin_cases first <;> fin_cases second <;> decide +kernel

end LeanTrominoes.OrthogonalDrawingRefinement
