import LeanTrominoes.PartrecDivision
import LeanTrominoes.PartrecNatCompareSpace

/-!
# Evaluator-space certificate for quotient and remainder

The numeric dividend drives a tail-recursive countdown.  Reachable states
retain one quotient, one remainder, and the unchanged divisor; the invariant
below bounds both live accumulators by the original dividend and therefore
lets every iteration reuse one input-linear workspace allowance.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def divisionAdvanceCost
    (quotient remainder divisor : Nat) : Nat :=
  prependCost [quotient, remainder, divisor]
    [quotient] [remainder + 1, divisor]
    (getCost 0 [quotient, remainder, divisor])
    (prependCost [quotient, remainder, divisor]
      [remainder + 1] [divisor]
      (succCost [remainder] +
        getCost 1 [quotient, remainder, divisor])
      (getCost 2 [quotient, remainder, divisor]))

theorem divisionAdvance
    (quotient remainder divisor : Nat) :
    EvaluatorCodeFits Code.divisionAdvanceCode
      [quotient, remainder, divisor]
      [quotient, remainder + 1, divisor]
      (divisionAdvanceCost quotient remainder divisor) := by
  have advanced :=
    comp (succ_named [remainder])
      (get 1 [quotient, remainder, divisor])
  have rest :=
    prepend advanced
      (get 2 [quotient, remainder, divisor])
  simpa [Code.divisionAdvanceCode,
    divisionAdvanceCost, prependCost] using
    prepend
      (get 0 [quotient, remainder, divisor]) rest

def divisionResetCost
    (quotient remainder divisor : Nat) : Nat :=
  prependCost [quotient, remainder, divisor]
    [quotient + 1] [0, divisor]
    (succCost [quotient] +
      getCost 0 [quotient, remainder, divisor])
    (prependCost [quotient, remainder, divisor]
      [0] [divisor]
      (zeroCost [quotient, remainder, divisor])
      (getCost 2 [quotient, remainder, divisor]))

theorem divisionReset
    (quotient remainder divisor : Nat) :
    EvaluatorCodeFits Code.divisionResetCode
      [quotient, remainder, divisor]
      [quotient + 1, 0, divisor]
      (divisionResetCost quotient remainder divisor) := by
  have incremented :=
    comp (succ_named [quotient])
      (get 0 [quotient, remainder, divisor])
  have rest :=
    prepend (zero [quotient, remainder, divisor])
      (get 2 [quotient, remainder, divisor])
  simpa [Code.divisionResetCode,
    divisionResetCost, prependCost] using
    prepend incremented rest

def divisionBelowArgumentsCost
    (quotient remainder divisor : Nat) : Nat :=
  prependCost [quotient, remainder, divisor]
    [remainder + 1] [divisor]
    (succCost [remainder] +
      getCost 1 [quotient, remainder, divisor])
    (getCost 2 [quotient, remainder, divisor])

theorem divisionBelowArguments
    (quotient remainder divisor : Nat) :
    EvaluatorCodeFits
      (Code.prepend (Code.succ.comp (Code.get 1))
        (Code.get 2))
      [quotient, remainder, divisor]
      [remainder + 1, divisor]
      (divisionBelowArgumentsCost
        quotient remainder divisor) := by
  simpa [divisionBelowArgumentsCost,
    prependCost] using
    prepend
      (comp (succ_named [remainder])
        (get 1 [quotient, remainder, divisor]))
      (get 2 [quotient, remainder, divisor])

def divisionBelowCost
    (quotient remainder divisor : Nat) : Nat :=
  natLtCost (remainder + 1) divisor +
    divisionBelowArgumentsCost quotient remainder divisor

theorem divisionBelow
    (quotient remainder divisor : Nat) :
    EvaluatorCodeFits Code.divisionBelowCode
      [quotient, remainder, divisor]
      [(decide (remainder + 1 < divisor)).toNat]
      (divisionBelowCost quotient remainder divisor) := by
  by_cases below : remainder + 1 < divisor <;>
    simpa [Code.divisionBelowCode, divisionBelowCost,
      below] using
      comp (natLt (remainder + 1) divisor)
        (divisionBelowArguments quotient remainder divisor)

def divisionInnerCost
    (quotient remainder divisor : Nat) : Nat :=
  if remainder + 1 < divisor then
    branchZeroSuccCost [quotient, remainder, divisor]
      [quotient, remainder + 1, divisor] 1
      (divisionBelowCost quotient remainder divisor)
      (divisionAdvanceCost quotient remainder divisor)
  else
    branchZeroZeroCost [quotient, remainder, divisor]
      [quotient + 1, 0, divisor] 0
      (divisionBelowCost quotient remainder divisor)
      (divisionResetCost quotient remainder divisor)

theorem divisionInner
    (quotient remainder divisor : Nat) :
    EvaluatorCodeFits
      (Code.branchZero Code.divisionBelowCode
        Code.divisionResetCode Code.divisionAdvanceCode)
      [quotient, remainder, divisor]
      (if remainder + 1 < divisor then
        [quotient, remainder + 1, divisor]
      else
        [quotient + 1, 0, divisor])
      (divisionInnerCost quotient remainder divisor) := by
  by_cases below : remainder + 1 < divisor
  · rw [if_pos below]
    have test :
        EvaluatorCodeFits Code.divisionBelowCode
          [quotient, remainder, divisor] [1]
          (divisionBelowCost quotient remainder divisor) := by
      simpa [below] using
        divisionBelow quotient remainder divisor
    simpa [divisionInnerCost, below] using
      branchZero_succ (show 0 < 1 by omega) test
        (divisionAdvance quotient remainder divisor)
  · rw [if_neg below]
    have test :
        EvaluatorCodeFits Code.divisionBelowCode
          [quotient, remainder, divisor] [0]
          (divisionBelowCost quotient remainder divisor) := by
      simpa [below] using
        divisionBelow quotient remainder divisor
    simpa [divisionInnerCost, below] using
      branchZero_zero rfl test
        (divisionReset quotient remainder divisor)

def divisionListStepCost
    (quotient remainder divisor : Nat) : Nat :=
  if divisor = 0 then
    branchZeroZeroCost [quotient, remainder, divisor]
      [quotient, remainder + 1, divisor] divisor
      (getCost 2 [quotient, remainder, divisor])
      (divisionAdvanceCost quotient remainder divisor)
  else
    branchZeroSuccCost [quotient, remainder, divisor]
      (if remainder + 1 < divisor then
        [quotient, remainder + 1, divisor]
      else
        [quotient + 1, 0, divisor])
      divisor (getCost 2 [quotient, remainder, divisor])
      (divisionInnerCost quotient remainder divisor)

theorem divisionListStep
    (quotient remainder divisor : Nat) :
    EvaluatorCodeFits Code.divisionListStepCode
      [quotient, remainder, divisor]
      (Code.divisionListStep
        [quotient, remainder, divisor])
      (divisionListStepCost
        quotient remainder divisor) := by
  by_cases divisorZero : divisor = 0
  · simpa [Code.divisionListStepCode,
      Code.divisionListStep, divisionListStepCost,
      divisorZero] using
      branchZero_zero divisorZero
        (get 2 [quotient, remainder, divisor])
        (divisionAdvance quotient remainder divisor)
  · have divisorPositive : 0 < divisor :=
      Nat.pos_of_ne_zero divisorZero
    simpa [Code.divisionListStepCode,
      Code.divisionListStep, divisionListStepCost,
      divisorZero] using
      branchZero_succ divisorPositive
        (get 2 [quotient, remainder, divisor])
        (divisionInner quotient remainder divisor)

def divisionBodyCost
    (remaining quotient remainder divisor : Nat) : Nat :=
  flatCountdownBodyCost Code.divisionListStep
    (fun _ =>
      divisionListStepCost quotient remainder divisor)
    remaining [quotient, remainder, divisor]

theorem divisionBody
    (remaining quotient remainder divisor : Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.divisionListStepCode)
      [remaining, quotient, remainder, divisor]
      (flatCountdownOutput Code.divisionListStep remaining
        [quotient, remainder, divisor])
      (divisionBodyCost
        remaining quotient remainder divisor) := by
  cases remaining with
  | zero =>
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, divisionBodyCost,
        flatCountdownBodyCost, zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one
              (.cons Code.head
                (Code.divisionListStepCode.comp Code.tail)))
          (values := [0, quotient, remainder, divisor])
          (by rfl)
          (zero'_named [quotient, remainder, divisor])
  | succ remaining =>
      let payload := [quotient, remainder, divisor]
      let values := remaining :: payload
      have transformed :=
        comp (divisionListStep quotient remainder divisor)
          (tail_named values)
      have payloadResult :=
        prepend (head values) transformed
      have branch :=
        prepend (one values) payloadResult
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, divisionBodyCost,
        flatCountdownBodyCost,
        flatCountdownSuccBranchCost,
        payload, values, prependCost,
        Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values :=
            (remaining + 1) :: payload)
          (predecessor := remaining)
          (by rfl) branch

def divisionLoopSpaceBound
    (number divisor : Nat) : Nat :=
  10000000000 *
    (encodedListSpace [8 * (number + divisor) + 16] + 1)

set_option maxHeartbeats 800000 in
theorem divisionBodyCost_le_input
    (number divisor remaining quotient remainder : Nat)
    (remainingBound : remaining ≤ number)
    (quotientBound : quotient ≤ number)
    (remainderBound : remainder ≤ number) :
    divisionBodyCost remaining quotient remainder divisor ≤
      divisionLoopSpaceBound number divisor := by
  let limit := 8 * (number + divisor) + 16
  have numberBound : number ≤ limit := by
    simp only [limit]
    omega
  have divisorBound : divisor ≤ limit := by
    simp only [limit]
    omega
  have remainingLimit : remaining ≤ limit :=
    remainingBound.trans numberBound
  have quotientLimit : quotient ≤ limit :=
    quotientBound.trans numberBound
  have remainderLimit : remainder ≤ limit :=
    remainderBound.trans numberBound
  have remainingBits := encodeNat_length_mono remainingLimit
  have remainingPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le remaining).trans remainingLimit)
  have quotientBits := encodeNat_length_mono quotientLimit
  have remainderBits := encodeNat_length_mono remainderLimit
  have divisorBits := encodeNat_length_mono divisorBound
  have divisorPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le divisor).trans divisorBound)
  have divisorSuccBits :=
    encodeNat_length_mono
      (show divisor + 1 ≤ limit by
        simp only [limit]
        omega)
  have quotientSuccBits :=
    encodeNat_length_mono
      (show quotient + 1 ≤ limit by
        simp only [limit]
        omega)
  have remainderSuccBits :=
    encodeNat_length_mono
      (show remainder + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have comparisonRaw :=
    natLtCost_le_linear (remainder + 1) divisor
  have comparisonSpace :
      encodedListSpace
          [2 * (remainder + 1 + divisor) + 4] ≤
        encodedListSpace [limit] := by
    have numeric :
        2 * (remainder + 1 + divisor) + 4 ≤ limit := by
      simp only [limit]
      omega
    simpa only [encodedListSpace_cons,
      encodedListSpace_nil, Nat.add_le_add_iff_right] using
      encodeNat_length_mono numeric
  have comparisonBound :
      natLtCost (remainder + 1) divisor ≤
        1000000000 *
          (encodedListSpace [limit] + 1) :=
    comparisonRaw.trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right
        comparisonSpace 1))
  clear comparisonRaw comparisonSpace
  have comparisonReserve :
      natLtCost (remainder + 1) divisor +
          1000000 * (encodedListSpace [limit] + 1) ≤
        divisionLoopSpaceBound number divisor := by
    change
      natLtCost (remainder + 1) divisor +
          1000000 * (encodedListSpace [limit] + 1) ≤
        10000000000 *
          (encodedListSpace [limit] + 1)
    omega
  clear comparisonBound
  have plumbing :
      divisionBodyCost remaining quotient remainder divisor ≤
        natLtCost (remainder + 1) divisor +
          1000000 * (encodedListSpace [limit] + 1) := by
    clear comparisonReserve
    by_cases divisorZero : divisor = 0 <;>
      by_cases below : remainder + 1 < divisor <;>
      cases remaining <;>
      simp [divisionBodyCost, divisionListStepCost,
        divisionInnerCost, divisionBelowCost,
        divisionBelowArgumentsCost, divisionResetCost,
        divisionAdvanceCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost,
        branchZeroZeroCost, branchZeroSuccCost,
        branchZeroTestCost,
        prependCost, getCost, dropCost, headCost,
        idCost, nilCost, zeroCost, oneCost,
        tailCost, zeroPrimeCost, succCost,
        Code.divisionListStep, divisorZero, below,
        encodedListSpace_cons, encodedListSpace_nil,
        limit, zeroBits, oneBits] at * <;>
      omega
  exact plumbing.trans comparisonReserve

/-- Reachable loop states, expressed only through the bounds needed by the
space proof. -/
def DivisionReachable
    (number divisor remaining : Nat)
    (values : List Nat) : Prop :=
  ∃ quotient remainder,
    values = [quotient, remainder, divisor] ∧
    remaining + quotient ≤ number ∧
    remaining + remainder ≤ number

theorem divisionReachable_initial
    (number divisor : Nat) :
    DivisionReachable number divisor number [0, 0, divisor] := by
  exact ⟨0, 0, rfl, by omega, by omega⟩

theorem divisionReachable_step
    (number divisor remaining : Nat)
    (values : List Nat)
    (reachable :
      DivisionReachable number divisor (remaining + 1) values) :
    DivisionReachable number divisor remaining
      (Code.divisionListStep values) := by
  obtain ⟨quotient, remainder, rfl,
    quotientBound, remainderBound⟩ := reachable
  by_cases divisorZero : divisor = 0 <;>
    by_cases below : remainder + 1 < divisor <;>
    simp [DivisionReachable, Code.divisionListStep,
      divisorZero, below] <;>
    omega

theorem divisionFlatUniform
    (number divisor : Nat) :
    EvaluatorCodeFits
      (Code.flatIterate Code.divisionListStepCode)
      [number, 0, 0, divisor]
      [number / divisor, number % divisor, divisor]
      (divisionLoopSpaceBound number divisor) where
  input_space := by
    exact
      (divisionBody number 0 0 divisor).input_space.trans
        (divisionBodyCost_le_input number divisor
          number 0 0 (Nat.le_refl _) (Nat.zero_le _)
          (Nat.zero_le _))
  output_space := by
    have finalBody :=
      divisionBody 0 (number / divisor)
        (number % divisor) divisor
    have quotientBound : number / divisor ≤ number :=
      Nat.div_le_self number divisor
    have remainderBound : number % divisor ≤ number :=
      Nat.mod_le number divisor
    have cost :=
      divisionBodyCost_le_input number divisor 0
        (number / divisor) (number % divisor)
        (Nat.zero_le _) quotientBound remainderBound
    have input := finalBody.input_space
    simp only [encodedListSpace_cons] at input ⊢
    omega
  call continuation bound budget after := by
    apply
      EvaluatorCallFits.flatIterate_of_reachable_code_fits
        (step := Code.divisionListStep)
        (bodyCost := fun _ _ =>
          divisionLoopSpaceBound number divisor)
        (invariant := DivisionReachable number divisor)
    · intro remaining values reachable
      obtain ⟨quotient, remainder, rfl,
        quotientBound, remainderBound⟩ := reachable
      exact
        (divisionBody remaining quotient remainder divisor).mono
          (divisionBodyCost_le_input number divisor
            remaining quotient remainder
            (by omega) (by omega) (by omega))
    · exact divisionReachable_initial number divisor
    · exact divisionReachable_step number divisor
    · intro remaining values reachable
      exact budget
    · rw [Code.divisionListStep_iterate_process,
        Code.divisionProcess_eq_div_mod]
      exact after

def divisionInputCost
    (number divisor : Nat) : Nat :=
  prependCost [number, divisor] [number] [0, 0, divisor]
    (getCost 0 [number, divisor])
    (prependCost [number, divisor] [0] [0, divisor]
      (zeroCost [number, divisor])
      (prependCost [number, divisor] [0] [divisor]
        (zeroCost [number, divisor])
        (getCost 1 [number, divisor])))

theorem divisionInput
    (number divisor : Nat) :
    EvaluatorCodeFits Code.divisionInputCode
      [number, divisor] [number, 0, 0, divisor]
      (divisionInputCost number divisor) := by
  simpa [Code.divisionInputCode,
    divisionInputCost, prependCost] using
    prepend (get 0 [number, divisor])
      (prepend (zero [number, divisor])
        (prepend (zero [number, divisor])
          (get 1 [number, divisor])))

def divisionProjectionCost
    (number divisor : Nat) : Nat :=
  prependCost
    [number / divisor, number % divisor, divisor]
    [number / divisor] [number % divisor]
    (getCost 0
      [number / divisor, number % divisor, divisor])
    (getCost 1
      [number / divisor, number % divisor, divisor])

theorem divisionProjection
    (number divisor : Nat) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 0) (Code.get 1))
      [number / divisor, number % divisor, divisor]
      [number / divisor, number % divisor]
      (divisionProjectionCost number divisor) := by
  simpa [divisionProjectionCost, prependCost] using
    prepend
      (get 0 [number / divisor, number % divisor, divisor])
      (get 1 [number / divisor, number % divisor, divisor])

def divisionUniformCost
    (number divisor : Nat) : Nat :=
  divisionProjectionCost number divisor +
    (divisionLoopSpaceBound number divisor +
      divisionInputCost number divisor)

theorem divisionUniform
    (number divisor : Nat) :
    EvaluatorCodeFits Code.divisionCode
      [number, divisor]
      [number / divisor, number % divisor]
      (divisionUniformCost number divisor) := by
  simpa [Code.divisionCode, divisionUniformCost] using
    comp (divisionProjection number divisor)
      (comp (divisionFlatUniform number divisor)
        (divisionInput number divisor))

def divisionSpaceBound
    (number divisor : Nat) : Nat :=
  100000000000 *
    (encodedListSpace [8 * (number + divisor) + 16] + 1)

set_option maxHeartbeats 800000 in
theorem divisionUniformCost_le_input
    (number divisor : Nat) :
    divisionUniformCost number divisor ≤
      divisionSpaceBound number divisor := by
  let limit := 8 * (number + divisor) + 16
  have numberBound : number ≤ limit := by
    simp only [limit]
    omega
  have divisorBound : divisor ≤ limit := by
    simp only [limit]
    omega
  have quotientNumber : number / divisor ≤ number :=
    Nat.div_le_self number divisor
  have remainderNumber : number % divisor ≤ number :=
    Nat.mod_le number divisor
  have quotientBound : number / divisor ≤ limit :=
    quotientNumber.trans numberBound
  have remainderBound : number % divisor ≤ limit :=
    remainderNumber.trans numberBound
  have numberBits := encodeNat_length_mono numberBound
  have divisorBits := encodeNat_length_mono divisorBound
  have quotientBits := encodeNat_length_mono quotientBound
  have remainderBits := encodeNat_length_mono remainderBound
  have numberSuccBits :=
    encodeNat_length_mono
      (show number + 1 ≤ limit by
        simp only [limit]
        omega)
  have divisorSuccBits :=
    encodeNat_length_mono
      (show divisor + 1 ≤ limit by
        simp only [limit]
        omega)
  have quotientSuccBits :=
    encodeNat_length_mono
      (show number / divisor + 1 ≤ limit by
        simp only [limit]
        omega)
  have remainderSuccBits :=
    encodeNat_length_mono
      (show number % divisor + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [divisionUniformCost, divisionProjectionCost,
    divisionInputCost, divisionLoopSpaceBound,
    divisionSpaceBound, prependCost, getCost, dropCost,
    headCost, idCost, nilCost, zeroCost, tailCost,
    zeroPrimeCost, succCost, encodedListSpace_cons,
    encodedListSpace_nil, limit, zeroBits] at *
  omega

theorem division
    (number divisor : Nat) :
    EvaluatorCodeFits Code.divisionCode
      [number, divisor]
      [number / divisor, number % divisor]
      (divisionSpaceBound number divisor) :=
  (divisionUniform number divisor).mono
    (divisionUniformCost_le_input number divisor)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
