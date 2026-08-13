/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

def boolOrCost
    (values : List Nat)
    (leftValue rightValue leftCost rightCost : Nat) : Nat :=
  if leftValue = 0 then
    branchZeroZeroCost values
      [if rightValue = 0 then 0 else 1]
      leftValue leftCost
      (normalizeBoolCost values rightValue rightCost)
  else
    branchZeroSuccCost values [1]
      leftValue leftCost (oneCost values)

theorem boolOr
    {left right : Code} {values : List Nat}
    {leftValue rightValue leftCost rightCost : Nat}
    (leftFits :
      EvaluatorCodeFits left values [leftValue] leftCost)
    (rightFits :
      EvaluatorCodeFits right values [rightValue] rightCost) :
    EvaluatorCodeFits (Code.boolOr left right) values
      [if leftValue = 0 ∧ rightValue = 0 then 0 else 1]
      (boolOrCost values leftValue rightValue
        leftCost rightCost) := by
  by_cases leftZero : leftValue = 0
  · have normalized := normalizeBool rightFits
    by_cases rightZero : rightValue = 0
    · rw [if_pos ⟨leftZero, rightZero⟩]
      simpa [Code.boolOr, boolOrCost,
        leftZero, rightZero] using
        branchZero_zero leftZero leftFits normalized
    · rw [if_neg (fun both => rightZero both.2)]
      simpa [Code.boolOr, boolOrCost,
        leftZero, rightZero] using
        branchZero_zero leftZero leftFits normalized
  · rw [if_neg (fun both => leftZero both.1)]
    simpa [Code.boolOr, boolOrCost, leftZero] using
      branchZero_succ
        (Nat.pos_of_ne_zero leftZero)
        leftFits (one values)

set_option maxHeartbeats 800000 in
theorem isZeroCost_le_budget
    (values : List Nat) (result valueCost budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (resultBound : encodedListSpace [result] ≤ budget)
    (predecessorBound :
      encodedListSpace [result.pred] ≤ budget)
    (headBound :
      (Computability.encodeNat values.headI).length ≤ budget)
    (headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget)
    (costBound : valueCost ≤ budget)
    (_positiveBudget : 1 ≤ budget) :
    isZeroCost values result valueCost ≤
      1000 * (budget + 1) := by
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  by_cases zeroResult : result = 0
  · subst result
    simp [isZeroCost, branchZeroZeroCost,
      branchZeroTestCost, prependCost, idCost,
      nilCost, zeroCost, oneCost, tailCost,
      zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at *
    omega
  · simp [isZeroCost, zeroResult,
      branchZeroSuccCost, branchZeroTestCost,
      prependCost, idCost, nilCost,
      zeroCost, tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at *
    omega

set_option maxHeartbeats 800000 in
theorem boolAndCost_le_budget
    (values : List Nat)
    (leftValue rightValue leftCost rightCost budget : Nat)
    (leftValueBound : leftValue ≤ 1)
    (rightValueBound : rightValue ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (headBound :
      (Computability.encodeNat values.headI).length ≤ budget)
    (headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget)
    (_positiveBudget : 1 ≤ budget) :
    boolAndCost values leftValue rightValue leftCost rightCost ≤
      1000 * (budget + 1) := by
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have leftCases : leftValue = 0 ∨ leftValue = 1 := by
    omega
  have rightCases : rightValue = 0 ∨ rightValue = 1 := by
    omega
  rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;>
    simp [boolAndCost, normalizeBoolCost,
      branchZeroZeroCost, branchZeroSuccCost,
      branchZeroTestCost, prependCost, idCost,
      nilCost, zeroCost, oneCost, tailCost,
      zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at * <;>
    omega

set_option maxHeartbeats 800000 in
theorem boolOrCost_le_budget
    (values : List Nat)
    (leftValue rightValue leftCost rightCost budget : Nat)
    (leftValueBound : leftValue ≤ 1)
    (rightValueBound : rightValue ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (headBound :
      (Computability.encodeNat values.headI).length ≤ budget)
    (headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget)
    (_positiveBudget : 1 ≤ budget) :
    boolOrCost values leftValue rightValue leftCost rightCost ≤
      1000 * (budget + 1) := by
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have leftCases : leftValue = 0 ∨ leftValue = 1 := by
    omega
  have rightCases : rightValue = 0 ∨ rightValue = 1 := by
    omega
  rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;>
    simp [boolOrCost, normalizeBoolCost,
      branchZeroZeroCost, branchZeroSuccCost,
      branchZeroTestCost, prependCost, idCost,
      nilCost, zeroCost, oneCost, tailCost,
      zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at * <;>
    omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
