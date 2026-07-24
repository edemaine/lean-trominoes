import LeanTrominoes.PartrecListCodeSpace

/-!
# Evaluator-space certificates for Boolean list combinators

Truth values are represented by naturals, with zero false and every positive
value true.  These certificates normalize such tags to zero or one and fit
short-circuiting conjunction.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def normalizeBoolCost
    (values : List Nat) (result valueCost : Nat) : Nat :=
  if result = 0 then
    branchZeroZeroCost values [0] result valueCost
      (zeroCost values)
  else
    branchZeroSuccCost values [1] result valueCost
      (oneCost values)

theorem normalizeBool
    {value : Code} {values : List Nat}
    {result valueCost : Nat}
    (valueFits :
      EvaluatorCodeFits value values [result] valueCost) :
    EvaluatorCodeFits (Code.normalizeBool value) values
      [if result = 0 then 0 else 1]
      (normalizeBoolCost values result valueCost) := by
  by_cases zeroResult : result = 0
  · rw [if_pos zeroResult]
    simpa [Code.normalizeBool, normalizeBoolCost,
      zeroResult] using
      branchZero_zero zeroResult valueFits (zero values)
  · rw [if_neg zeroResult]
    simpa [Code.normalizeBool, normalizeBoolCost,
      zeroResult] using
      branchZero_succ (Nat.pos_of_ne_zero zeroResult)
        valueFits (one values)

def isZeroCost
    (values : List Nat) (result valueCost : Nat) : Nat :=
  if result = 0 then
    branchZeroZeroCost values [1] result valueCost
      (oneCost values)
  else
    branchZeroSuccCost values [0] result valueCost
      (zeroCost values)

theorem isZero
    {value : Code} {values : List Nat}
    {result valueCost : Nat}
    (valueFits :
      EvaluatorCodeFits value values [result] valueCost) :
    EvaluatorCodeFits (Code.isZero value) values
      [if result = 0 then 1 else 0]
      (isZeroCost values result valueCost) := by
  by_cases zeroResult : result = 0
  · rw [if_pos zeroResult]
    simpa [Code.isZero, isZeroCost,
      zeroResult] using
      branchZero_zero zeroResult valueFits (one values)
  · rw [if_neg zeroResult]
    simpa [Code.isZero, isZeroCost,
      zeroResult] using
      branchZero_succ (Nat.pos_of_ne_zero zeroResult)
        valueFits (zero values)

def boolAndCost
    (values : List Nat)
    (leftValue rightValue leftCost rightCost : Nat) : Nat :=
  if leftValue = 0 then
    branchZeroZeroCost values [0]
      leftValue leftCost (zeroCost values)
  else
    branchZeroSuccCost values
      [if rightValue = 0 then 0 else 1]
      leftValue leftCost
      (normalizeBoolCost values rightValue rightCost)

theorem boolAnd
    {left right : Code} {values : List Nat}
    {leftValue rightValue leftCost rightCost : Nat}
    (leftFits :
      EvaluatorCodeFits left values [leftValue] leftCost)
    (rightFits :
      EvaluatorCodeFits right values [rightValue] rightCost) :
    EvaluatorCodeFits (Code.boolAnd left right) values
      [if leftValue = 0 ∨ rightValue = 0 then 0 else 1]
      (boolAndCost values leftValue rightValue
        leftCost rightCost) := by
  by_cases leftZero : leftValue = 0
  · rw [if_pos (Or.inl leftZero)]
    simpa [Code.boolAnd, boolAndCost, leftZero] using
      branchZero_zero leftZero leftFits (zero values)
  · have normalized := normalizeBool rightFits
    by_cases rightZero : rightValue = 0
    · rw [if_pos (Or.inr rightZero)]
      simpa [Code.boolAnd, boolAndCost,
        leftZero, rightZero] using
        branchZero_succ
          (Nat.pos_of_ne_zero leftZero)
          leftFits normalized
    · rw [if_neg (not_or_intro leftZero rightZero)]
      simpa [Code.boolAnd, boolAndCost,
        leftZero, rightZero] using
        branchZero_succ
          (Nat.pos_of_ne_zero leftZero)
          leftFits normalized

end EvaluatorCodeFits

end PartrecToTM2
end Turing
