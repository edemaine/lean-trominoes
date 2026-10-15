/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawing
import Mathlib.Tactic

/-! # The ten boundary anchors of a vertex rectangle -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

structure AnchorProfile where
  leftCount : Fin 5
  rightCount : Fin 5
  top : Bool
  bottom : Bool
  deriving DecidableEq, Repr

def AnchorProfile.degree (profile : AnchorProfile) : Nat :=
  profile.leftCount.val+profile.rightCount.val+(if profile.top then 1 else 0)+(if profile.bottom then 1 else 0)

/-- Clockwise order: right anchors descend, left anchors ascend. -/
def AnchorProfile.anchors (profile : AnchorProfile) : List Cell :=
  (List.range profile.rightCount.val).map (fun rank => (5,7-2*(rank : Int))) ++
    (if profile.bottom then [(0,-10)] else []) ++
    (List.range profile.leftCount.val).map (fun rank => (-5,-7+2*(rank : Int))) ++
    (if profile.top then [(0,10)] else [])

theorem AnchorProfile.anchors_length (profile : AnchorProfile) : profile.anchors.length = profile.degree := by
  cases profile with
  | mk left right top bottom =>
    cases top <;> cases bottom <;> simp [anchors,degree] <;> omega

theorem AnchorProfile.anchors_nodup (profile : AnchorProfile) : profile.anchors.Nodup := by
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> decide +kernel

theorem AnchorProfile.anchors_on_boundary (profile : AnchorProfile) :
    ∀ point ∈ profile.anchors,
      (-5 ≤ point.1 ∧ point.1 ≤ 5 ∧ -10 ≤ point.2 ∧ point.2 ≤ 10) ∧
        (point.1 = -5 ∨ point.1 = 5 ∨ point.2 = -10 ∨ point.2 = 10) := by
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> decide +kernel

end LeanTrominoes.OrthogonalDrawingRefinement
