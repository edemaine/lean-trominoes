import LeanTrominoes.PartrecCodeSpace
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecListCode

/-!
# Evaluator-space costs for direct list combinators

This module lifts the total list combinators used by the explicit strip
program to `EvaluatorCodeFits`.  Costs are intentionally generous sums of
the component certificates; later strip-specific lemmas bound those sums by
one polynomial envelope.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def zeroPrimeCost (values : List Nat) : Nat :=
  encodedListSpace values +
    encodedListSpace (0 :: values) + 1

def tailCost (values : List Nat) : Nat :=
  encodedListSpace values +
    encodedListSpace values.tail + 1

def succCost (values : List Nat) : Nat :=
  encodedListSpace values +
    encodedListSpace [values.headI] +
    encodedListSpace [values.headI.succ] + 2

theorem zero'_named (values : List Nat) :
    EvaluatorCodeFits Code.zero' values (0 :: values)
      (zeroPrimeCost values) := by
  simpa [zeroPrimeCost] using EvaluatorCodeFits.zero' values

theorem tail_named (values : List Nat) :
    EvaluatorCodeFits Code.tail values values.tail
      (tailCost values) := by
  simpa [tailCost] using EvaluatorCodeFits.tail values

theorem succ_named (values : List Nat) :
    EvaluatorCodeFits Code.succ values [values.headI.succ]
      (succCost values) := by
  simpa [succCost] using EvaluatorCodeFits.succ values

def idCost (values : List Nat) : Nat :=
  tailCost (0 :: values) + zeroPrimeCost values

theorem id (values : List Nat) :
    EvaluatorCodeFits Code.id values values (idCost values) := by
  simpa [Code.id, idCost] using
    EvaluatorCodeFits.comp
      (tail_named (0 :: values))
      (zero'_named values)

def nilCost (values : List Nat) : Nat :=
  tailCost [values.headI.succ] + succCost values

theorem nil (values : List Nat) :
    EvaluatorCodeFits Code.nil values [] (nilCost values) := by
  simpa [Code.nil, nilCost] using
    EvaluatorCodeFits.comp
      (tail_named [values.headI.succ])
      (succ_named values)

def headCost (values : List Nat) : Nat :=
  idCost values + nilCost values +
    encodedListSpace values + encodedListSpace values +
      encodedListSpace [values.headI] + 2

theorem head (values : List Nat) :
    EvaluatorCodeFits Code.head values [values.headI]
      (headCost values) := by
  simpa [Code.head, headCost] using
    EvaluatorCodeFits.cons (id values) (nil values)

def zeroCost (values : List Nat) : Nat :=
  zeroPrimeCost values + nilCost values +
    encodedListSpace values + encodedListSpace (0 :: values) +
      encodedListSpace [0] + 2

theorem zero (values : List Nat) :
    EvaluatorCodeFits Code.zero values [0] (zeroCost values) := by
  simpa [Code.zero, zeroCost] using
    EvaluatorCodeFits.cons (zero'_named values) (nil values)

def oneCost (values : List Nat) : Nat :=
  succCost [0] + zeroCost values

theorem one (values : List Nat) :
    EvaluatorCodeFits Code.one values [1] (oneCost values) := by
  simpa [Code.one, oneCost] using
    EvaluatorCodeFits.comp
      (succ_named [0])
      (zero values)

def dropCost : Nat → List Nat → Nat
  | 0, values => idCost values
  | count + 1, values =>
      dropCost count values.tail + tailCost values

theorem drop (count : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.drop count) values
      (values.drop count) (dropCost count values) := by
  induction count generalizing values with
  | zero =>
      simpa [Code.drop, dropCost] using id values
  | succ count induction =>
      simpa [Code.drop, dropCost] using
        EvaluatorCodeFits.comp
          (induction values.tail)
          (tail_named values)

def getCost (index : Nat) (values : List Nat) : Nat :=
  headCost (values.drop index) + dropCost index values

theorem get (index : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.get index) values
      [values[index]?.getD 0] (getCost index values) := by
  have headAfterDrop :
      (values.drop index).headI = values[index]?.getD 0 := by
    induction index generalizing values with
    | zero =>
        cases values <;> rfl
    | succ index induction =>
        cases values with
        | nil => simp
        | cons value values =>
            simpa using induction values
  simpa [Code.get, getCost, headAfterDrop] using
    EvaluatorCodeFits.comp
      (head (values.drop index))
      (drop index values)

def addConstCost : Nat → List Nat → Nat
  | 0, values => headCost values
  | increment + 1, values =>
      succCost [values.headI + increment] +
        addConstCost increment values

theorem addConst (increment : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.addConst increment) values
      [values.headI + increment]
      (addConstCost increment values) := by
  induction increment with
  | zero =>
      simpa [Code.addConst, addConstCost] using head values
  | succ increment induction =>
      simpa [Code.addConst, addConstCost, Nat.add_assoc] using
        EvaluatorCodeFits.comp
          (succ_named [values.headI + increment])
          induction

def numeralCost (value : Nat) (values : List Nat) : Nat :=
  addConstCost value [0] + zeroCost values

theorem numeral (value : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.numeral value) values [value]
      (numeralCost value values) := by
  simpa [Code.numeral, numeralCost] using
    EvaluatorCodeFits.comp
      (addConst value [0])
      (zero values)

def prependCost
    (values fieldOutput restOutput : List Nat)
    (fieldCost restCost : Nat) : Nat :=
  fieldCost + restCost +
    encodedListSpace values +
    encodedListSpace fieldOutput +
    encodedListSpace (fieldOutput.headI :: restOutput) + 2

theorem prepend
    {field rest : Code} {values fieldOutput restOutput : List Nat}
    {fieldCost restCost : Nat}
    (fieldFits :
      EvaluatorCodeFits field values fieldOutput fieldCost)
    (restFits :
      EvaluatorCodeFits rest values restOutput restCost) :
    EvaluatorCodeFits (Code.prepend field rest) values
      (fieldOutput.headI :: restOutput)
      (prependCost values fieldOutput restOutput
        fieldCost restCost) := by
  simpa [Code.prepend, prependCost] using
    EvaluatorCodeFits.cons fieldFits restFits

def branchZeroTestCost
    (values : List Nat) (testValue testCost : Nat) : Nat :=
  prependCost values [testValue] values
    testCost (idCost values)

def branchZeroZeroCost
    (values output : List Nat)
    (testValue testCost branchCost : Nat) : Nat :=
  (branchCost +
      encodedListSpace (testValue :: values) +
      encodedListSpace output + 1) +
    branchZeroTestCost values testValue testCost

theorem branchZero_zero
    {test whenZero whenSucc : Code}
    {values output : List Nat} {testValue testCost branchCost : Nat}
    (zero : testValue = 0)
    (testFits :
      EvaluatorCodeFits test values [testValue] testCost)
    (branchFits :
      EvaluatorCodeFits whenZero values output branchCost) :
    EvaluatorCodeFits
      (Code.branchZero test whenZero whenSucc)
      values output
      (branchZeroZeroCost values output
        testValue testCost branchCost) := by
  have tested :=
    prepend testFits (id values)
  have selected :
      EvaluatorCodeFits
        (.case whenZero (whenSucc.comp Code.tail))
        (testValue :: values) output
        (branchCost +
          encodedListSpace (testValue :: values) +
          encodedListSpace output + 1) :=
    EvaluatorCodeFits.case_zero
      (successorBranch := whenSucc.comp Code.tail)
      (values := testValue :: values)
      (by simp [zero])
      branchFits
  simpa [Code.branchZero, Code.prepend, branchZeroZeroCost,
    branchZeroTestCost] using
      EvaluatorCodeFits.comp selected tested

def branchZeroSuccCost
    (values output : List Nat)
    (testValue testCost branchCost : Nat) : Nat :=
  ((branchCost + tailCost (testValue.pred :: values)) +
      encodedListSpace (testValue :: values) +
      encodedListSpace output + 1) +
    branchZeroTestCost values testValue testCost

theorem branchZero_succ
    {test whenZero whenSucc : Code}
    {values output : List Nat}
    {testValue testCost branchCost : Nat}
    (positive : 0 < testValue)
    (testFits :
      EvaluatorCodeFits test values [testValue] testCost)
    (branchFits :
      EvaluatorCodeFits whenSucc values output branchCost) :
    EvaluatorCodeFits
      (Code.branchZero test whenZero whenSucc)
      values output
      (branchZeroSuccCost values output
        testValue testCost branchCost) := by
  have predecessor :
      testValue = testValue.pred + 1 := by
    exact (Nat.succ_pred_eq_of_pos positive).symm
  have tested :=
    prepend testFits (id values)
  have tailThenBranch :=
    EvaluatorCodeFits.comp branchFits
      (tail_named (testValue.pred :: values))
  have selected :
      EvaluatorCodeFits
        (.case whenZero (whenSucc.comp Code.tail))
        (testValue :: values) output
        ((branchCost + tailCost (testValue.pred :: values)) +
          encodedListSpace (testValue :: values) +
          encodedListSpace output + 1) :=
    EvaluatorCodeFits.case_succ
      (zeroBranch := whenZero)
      (values := testValue :: values)
      (predecessor := testValue.pred)
      (by simp only [List.headI_cons]; exact predecessor)
      tailThenBranch
  simpa [Code.branchZero, Code.prepend, branchZeroSuccCost,
    branchZeroTestCost] using
      EvaluatorCodeFits.comp selected tested

def flatCountdownSuccBranchCost
    (step : List Nat → List Nat)
    (stepCost : List Nat → Nat)
    (remaining : Nat) (payload : List Nat) : Nat :=
  let values := remaining :: payload
  let transformedCost :=
    stepCost payload + tailCost values
  let payloadCost :=
    prependCost values [remaining] (step payload)
      (headCost values) transformedCost
  prependCost values [1] (remaining :: step payload)
    (oneCost values) payloadCost

def flatCountdownBodyCost
    (step : List Nat → List Nat)
    (stepCost : List Nat → Nat) :
    Nat → List Nat → Nat
  | 0, payload =>
      zeroPrimeCost payload +
        encodedListSpace (0 :: payload) +
        encodedListSpace (0 :: payload) + 1
  | remaining + 1, payload =>
      flatCountdownSuccBranchCost step stepCost remaining payload +
        encodedListSpace ((remaining + 1) :: payload) +
        encodedListSpace (1 :: remaining :: step payload) + 1

/-- Lift a finite data-cost certificate for one payload transformation to one
tagged flat-countdown body call. -/
theorem flatCountdownBody
    {stepCode : Code} {step : List Nat → List Nat}
    {stepCost : List Nat → Nat}
    (stepFits :
      ∀ payload,
        EvaluatorCodeFits stepCode payload
          (step payload) (stepCost payload))
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits (Code.flatCountdownBody stepCode)
      (remaining :: payload)
      (flatCountdownOutput step remaining payload)
      (flatCountdownBodyCost step stepCost remaining payload) := by
  cases remaining with
  | zero =>
      simpa [Code.flatCountdownBody, flatCountdownOutput,
        flatCountdownBodyCost, zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one
              (.cons Code.head (stepCode.comp Code.tail)))
          (values := 0 :: payload)
          (by rfl)
          (zero'_named payload)
  | succ remaining =>
      let values := remaining :: payload
      have transformed :=
        EvaluatorCodeFits.comp
          (stepFits payload)
          (tail_named values)
      have payloadResult :=
        prepend (head values) transformed
      have branch :=
        prepend (one values) payloadResult
      simpa [Code.flatCountdownBody, flatCountdownOutput,
        flatCountdownBodyCost, flatCountdownSuccBranchCost,
        values, prependCost, Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values := (remaining + 1) :: payload)
          (predecessor := remaining)
          (by rfl)
          branch

end EvaluatorCodeFits

end PartrecToTM2
end Turing
