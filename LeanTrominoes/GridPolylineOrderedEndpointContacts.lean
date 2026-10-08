/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealOpenSimple

/-! # Original parameter order rules out nonadjacent shared endpoints -/
namespace LeanTrominoes.GridPolyline

theorem ordered_endpoint_contact {first last : List Cell} {firstStart firstFinish lastStart lastFinish : ℚ}
    (firstPositive : firstStart < firstFinish) (lastPositive : lastStart < lastFinish)
    (ordered : firstFinish ≤ lastStart)
    (parametersAgree : ∀ firstExit lastExit : Bool,
      (if firstExit then first.getLast? else first.head?) = (if lastExit then last.getLast? else last.head?) →
      (if firstExit then firstFinish else firstStart) = (if lastExit then lastFinish else lastStart))
    {point : ℝ × ℝ} (firstEndpoint : RealIsEndpoint first point) (lastEndpoint : RealIsEndpoint last point) :
    firstFinish = lastStart ∧ point = realCell (first.getLast?.getD (0,0)) := by
  rcases firstEndpoint with ⟨firstPoint,firstEnd,firstReal⟩ | ⟨firstPoint,firstEnd,firstReal⟩ <;>
    rcases lastEndpoint with ⟨lastPoint,lastEnd,lastReal⟩ | ⟨lastPoint,lastEnd,lastReal⟩
  all_goals have points := realCell_injective (firstReal.symm.trans lastReal)
  · have parameters := parametersAgree false false (firstEnd.trans ((congrArg some points).trans lastEnd.symm))
    simp only [Bool.false_eq_true,if_false] at parameters
    linarith
  · have parameters := parametersAgree false true (firstEnd.trans ((congrArg some points).trans lastEnd.symm))
    simp only [Bool.false_eq_true,if_false,if_true] at parameters
    linarith
  · have parameters := parametersAgree true false (firstEnd.trans ((congrArg some points).trans lastEnd.symm))
    refine ⟨parameters,?_⟩
    simpa only [firstEnd,Option.getD_some] using firstReal
  · have parameters := parametersAgree true true (firstEnd.trans ((congrArg some points).trans lastEnd.symm))
    simp only [if_true] at parameters
    linarith

end LeanTrominoes.GridPolyline
