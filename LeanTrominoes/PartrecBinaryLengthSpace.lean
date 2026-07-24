import LeanTrominoes.PartrecBinaryLength
import LeanTrominoes.PartrecListCodeSpace
import Mathlib.Data.Nat.Size

/-!
# Evaluator-space costs for explicit binary length

This module supplies compositional finite-call certificates for the concrete
list programs in `PartrecBinaryLength`.  The subsequent loop certificates use
the invariants of division by two and binary-length iteration to keep these
costs polynomial in the original binary input length.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

private theorem encodeNat_eq_bits (number : Nat) :
    Computability.encodeNat number = number.bits := by
  induction number using Nat.binaryRec' with
  | zero =>
      rfl
  | bit bit number nonzero induction =>
      rw [LeanTrominoes.Computability.encodeNat_cons
        (Nat.bit bit number)
          (Nat.pos_of_ne_zero
            (Nat.bit_ne_zero_iff.mpr nonzero))]
      simp only [Nat.bodd_bit, Nat.div2_bit,
        Nat.bits_append_bit number bit nonzero]
      rw [induction]

theorem encodeNat_length_mono
    {smaller larger : Nat} (bounded : smaller ≤ larger) :
    (Computability.encodeNat smaller).length ≤
      (Computability.encodeNat larger).length := by
  rw [encodeNat_eq_bits, encodeNat_eq_bits,
    Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size bounded

theorem encodeNat_succ_length_le (number : Nat) :
    (Computability.encodeNat number.succ).length ≤
      (Computability.encodeNat number).length + 1 := by
  rw [encodeNat_eq_bits, encodeNat_eq_bits,
    Nat.size_eq_bits_len, Nat.size_eq_bits_len,
    Nat.size_le]
  have current := Nat.lt_size_self number
  rw [pow_succ]
  omega

theorem encodedListSpace_tail_le (values : List Nat) :
    encodedListSpace values.tail ≤ encodedListSpace values := by
  cases values <;> simp [encodedListSpace_cons]

theorem encodedListSpace_singleton_headI_le (values : List Nat) :
    encodedListSpace [values.headI] ≤
      encodedListSpace values + 1 := by
  cases values with
  | nil =>
      rfl
  | cons head tail =>
      simp only [List.headI_cons, encodedListSpace_cons,
        encodedListSpace_nil]
      omega

theorem encodedListSpace_singleton_tail_headI_le
    (values : List Nat) :
    encodedListSpace [values.tail.headI] ≤
      encodedListSpace values + 1 := by
  cases values with
  | nil =>
      rfl
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.tail_cons, List.headI_nil,
            encodedListSpace_cons, encodedListSpace_nil]
          change 1 ≤ _ + 1
          omega
      | cons next rest =>
          simp only [List.tail_cons, List.headI_cons,
            encodedListSpace_cons, encodedListSpace_nil]
          omega

namespace EvaluatorCodeFits

private theorem getD_zero_eq_headI (values : List Nat) :
    values[0]?.getD 0 = values.headI := by
  cases values <;> rfl

private theorem getD_one_eq_tail_headI (values : List Nat) :
    values[1]?.getD 0 = values.tail.headI := by
  cases values with
  | nil => rfl
  | cons head tail =>
      cases tail <;> rfl

def binaryDiv2ZeroBranchCost (values : List Nat) : Nat :=
  let restCost :=
    prependCost values [1] []
      (oneCost values) (nilCost values)
  prependCost values [values.headI] [1]
    (getCost 0 values) restCost

def binaryDiv2SuccBranchCost (values : List Nat) : Nat :=
  let fieldCost :=
    succCost [values.headI] + getCost 0 values
  let restCost :=
    prependCost values [0] []
      (zeroCost values) (nilCost values)
  prependCost values [values.headI.succ] [0]
    fieldCost restCost

def binaryDiv2ListStepCost (values : List Nat) : Nat :=
  if values[1]?.getD 0 = 0 then
    branchZeroZeroCost values
      (Code.binaryDiv2ListStep values)
      (values[1]?.getD 0) (getCost 1 values)
      (binaryDiv2ZeroBranchCost values)
  else
    branchZeroSuccCost values
      (Code.binaryDiv2ListStep values)
      (values[1]?.getD 0) (getCost 1 values)
      (binaryDiv2SuccBranchCost values)

theorem binaryDiv2ListStepCode (values : List Nat) :
    EvaluatorCodeFits Code.binaryDiv2ListStepCode values
      (Code.binaryDiv2ListStep values)
      (binaryDiv2ListStepCost values) := by
  have testFits :
      EvaluatorCodeFits (Code.get 1) values
        [values[1]?.getD 0] (getCost 1 values) :=
    get 1 values
  by_cases parityZero : values[1]?.getD 0 = 0
  · have rest :=
      prepend (one values) (nil values)
    have branch :=
      prepend
        (by
          simpa [getD_zero_eq_headI] using get 0 values)
        rest
    simpa [Code.binaryDiv2ListStepCode,
      Code.binaryDiv2ListStep, binaryDiv2ListStepCost,
      parityZero, binaryDiv2ZeroBranchCost, Code.prepend,
      prependCost] using
        branchZero_zero parityZero testFits branch
  · have positive := Nat.pos_of_ne_zero parityZero
    have field :=
      EvaluatorCodeFits.comp
        (succ_named [values.headI])
        (by
          simpa [getD_zero_eq_headI] using get 0 values)
    have rest :=
      prepend (zero values) (nil values)
    have branch :=
      prepend field rest
    simpa [Code.binaryDiv2ListStepCode,
      Code.binaryDiv2ListStep, binaryDiv2ListStepCost,
      parityZero, binaryDiv2SuccBranchCost, Code.prepend,
      prependCost] using
        branchZero_succ positive testFits branch

def binaryDiv2InputCost (values : List Nat) : Nat :=
  let finalCost :=
    prependCost values [0] []
      (zeroCost values) (nilCost values)
  let parityCost :=
    prependCost values [0] [0]
      (zeroCost values) finalCost
  prependCost values [values.headI] [0, 0]
    (getCost 0 values) parityCost

theorem binaryDiv2InputCode (values : List Nat) :
    EvaluatorCodeFits Code.binaryDiv2InputCode values
      [values.headI, 0, 0] (binaryDiv2InputCost values) := by
  have final :=
    prepend (zero values) (nil values)
  have parity :=
    prepend (zero values) final
  have number :=
    prepend
      (by
        simpa [getD_zero_eq_headI] using get 0 values)
      parity
  simpa [Code.binaryDiv2InputCode, binaryDiv2InputCost,
    Code.prepend, prependCost] using number

/-- One division-step call has linear data cost in its two-field input. -/
theorem binaryDiv2ListStepCost_le (values : List Nat) :
    binaryDiv2ListStepCost values ≤
      10000 * (encodedListSpace values + 1) := by
  have headSpace :=
    encodedListSpace_singleton_headI_le values
  have tailHeadSpace :=
    encodedListSpace_singleton_tail_headI_le values
  have tailSpace := encodedListSpace_tail_le values
  have headBits :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have tailHeadBits :
      (Computability.encodeNat values.tail.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using tailHeadSpace
  have successorBits :=
    encodeNat_succ_length_le values.headI
  have headPlusBits :
      (Computability.encodeNat (values.headI + 1)).length ≤
        (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successorBits
  have tailSuccessorBits :=
    encodeNat_succ_length_le values.tail.headI
  have tailPlusBits :
      (Computability.encodeNat
        (values.tail.headI + 1)).length ≤
          (Computability.encodeNat values.tail.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using tailSuccessorBits
  have predecessorBits :=
    encodeNat_length_mono
      (Nat.pred_le (values[1]?.getD 0))
  have predecessorBits' :
      (Computability.encodeNat
        (values[1]?.getD 0 - 1)).length ≤
          (Computability.encodeNat
            (values[1]?.getD 0)).length := by
    simpa [Nat.pred_eq_sub_one] using predecessorBits
  have testBits :
      (Computability.encodeNat
        (values[1]?.getD 0)).length + 1 ≤
          encodedListSpace values + 1 := by
    rw [getD_one_eq_tail_headI]
    simpa [encodedListSpace_cons] using tailHeadSpace
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  by_cases parityZero : values[1]?.getD 0 = 0
  · rw [binaryDiv2ListStepCost, if_pos parityZero]
    simp [branchZeroZeroCost, branchZeroTestCost,
      binaryDiv2ZeroBranchCost, prependCost, getCost,
      dropCost, idCost, headCost, nilCost, oneCost,
      zeroCost, zeroPrimeCost, tailCost, succCost,
      Code.binaryDiv2ListStep, parityZero,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits]
    omega
  · rw [binaryDiv2ListStepCost, if_neg parityZero]
    simp [branchZeroSuccCost, branchZeroTestCost,
      binaryDiv2SuccBranchCost, prependCost, getCost,
      dropCost, idCost, headCost, nilCost,
      zeroCost, zeroPrimeCost, tailCost, succCost,
      Code.binaryDiv2ListStep, parityZero,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits]
    omega

theorem getZeroCost_le (values : List Nat) :
    getCost 0 values ≤
      10000 * (encodedListSpace values + 1) := by
  have headSpace :=
    encodedListSpace_singleton_headI_le values
  have headBits :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits :=
    encodeNat_succ_length_le values.headI
  have headPlusBits :
      (Computability.encodeNat (values.headI + 1)).length ≤
        (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [getCost, dropCost, idCost, headCost, nilCost,
    zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil, zeroBits]
  omega

theorem binaryDiv2InputCost_le (values : List Nat) :
    binaryDiv2InputCost values ≤
      100000 * (encodedListSpace values + 1) := by
  have headSpace :=
    encodedListSpace_singleton_headI_le values
  have headBits :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits :=
    encodeNat_succ_length_le values.headI
  have headPlusBits :
      (Computability.encodeNat (values.headI + 1)).length ≤
        (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  simp [binaryDiv2InputCost, prependCost, getCost,
    dropCost, idCost, headCost, nilCost, zeroCost,
    zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits]
  omega

def binaryDiv2BodyCost (remaining : Nat)
    (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.binaryDiv2ListStep
    binaryDiv2ListStepCost remaining payload

theorem binaryDiv2Body
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.binaryDiv2ListStepCode)
      (remaining :: payload)
      (flatCountdownOutput Code.binaryDiv2ListStep
        remaining payload)
      (binaryDiv2BodyCost remaining payload) := by
  simpa [binaryDiv2BodyCost] using
    flatCountdownBody binaryDiv2ListStepCode
      remaining payload

theorem binaryDiv2BodyCost_le
    (remaining : Nat) (payload : List Nat) :
    binaryDiv2BodyCost remaining payload ≤
      1000000 *
        (encodedListSpace (remaining :: payload) +
          encodedListSpace
            (Code.binaryDiv2ListStep payload) + 1) := by
  have stepCost := binaryDiv2ListStepCost_le payload
  have valuesHeadSpace :=
    encodedListSpace_singleton_headI_le
      (remaining :: payload)
  have valuesSuccessorBits :=
    encodeNat_succ_length_le remaining
  have valuesHeadPlusBits :
      (Computability.encodeNat (remaining + 1)).length ≤
        (Computability.encodeNat remaining).length + 1 := by
    simpa [Nat.succ_eq_add_one] using valuesSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [binaryDiv2BodyCost, flatCountdownBodyCost,
        zeroPrimeCost, encodedListSpace_cons, zeroBits]
      omega
  | succ remaining =>
      rw [encodedListSpace_cons]
      have predecessorBits :
          (Computability.encodeNat remaining).length ≤
            (Computability.encodeNat (remaining + 1)).length :=
        encodeNat_length_mono (Nat.le_succ remaining)
      simp [binaryDiv2BodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, prependCost,
        idCost, headCost, nilCost, oneCost,
        zeroCost, zeroPrimeCost, tailCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits]
      omega

def binaryDiv2Invariant (number remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = number ∧
      payload =
        (Code.binaryDiv2ListStep^[processed]) [0, 0]

theorem binaryDiv2Invariant_initial (number : Nat) :
    binaryDiv2Invariant number number [0, 0] := by
  exact ⟨0, by simp, rfl⟩

theorem binaryDiv2Invariant_preserved
    (number remaining : Nat) (payload : List Nat)
    (invariant :
      binaryDiv2Invariant number (remaining + 1) payload) :
    binaryDiv2Invariant number remaining
      (Code.binaryDiv2ListStep payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']

def binaryDiv2Cost (number : Nat) : Nat :=
  10000000 * (encodedListSpace [number] + 1)

theorem binaryDiv2BodyCost_le_total
    (number remaining : Nat) (payload : List Nat)
    (invariant :
      binaryDiv2Invariant number remaining payload) :
    binaryDiv2BodyCost remaining payload ≤
      binaryDiv2Cost number := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have processedBound : processed ≤ number := by omega
  have remainingBound : remaining ≤ number := by omega
  have nextBound : processed + 1 ≤ number + 1 := by omega
  have quotientLe : processed.div2 ≤ processed := by
    have identity := Nat.bodd_add_div2 processed
    omega
  have quotientBound : processed.div2 ≤ number :=
    quotientLe.trans processedBound
  have nextQuotientLe :
      (processed + 1).div2 ≤ processed + 1 := by
    have identity := Nat.bodd_add_div2 (processed + 1)
    omega
  have nextQuotientBound :
      (processed + 1).div2 ≤ number + 1 :=
    nextQuotientLe.trans nextBound
  have remainingBits :=
    encodeNat_length_mono remainingBound
  have quotientBits :=
    encodeNat_length_mono quotientBound
  have nextNumberBits :=
    encodeNat_succ_length_le number
  have nextQuotientBits :=
    (encodeNat_length_mono nextQuotientBound).trans
      nextNumberBits
  have parityBound :
      processed.bodd.toNat ≤ 1 := by
    cases processed.bodd <;> decide
  have nextParityBound :
      (processed + 1).bodd.toNat ≤ 1 := by
    cases (processed + 1).bodd <;> decide
  have parityBits :=
    encodeNat_length_mono parityBound
  have nextParityBits :=
    encodeNat_length_mono nextParityBound
  have nextPayload :
      Code.binaryDiv2ListStep
          ((Code.binaryDiv2ListStep^[processed]) [0, 0]) =
        (Code.binaryDiv2ListStep^[processed + 1]) [0, 0] := by
    rw [Function.iterate_succ_apply']
  have bodyBound :=
    binaryDiv2BodyCost_le remaining
      ((Code.binaryDiv2ListStep^[processed]) [0, 0])
  rw [nextPayload,
    Code.binaryDiv2ListStep_iterate processed,
    Code.binaryDiv2ListStep_iterate (processed + 1)] at bodyBound
  simp only [encodedListSpace_cons, encodedListSpace_nil] at bodyBound
  rw [Code.binaryDiv2ListStep_iterate processed]
  simp only [binaryDiv2Cost, encodedListSpace_cons,
    encodedListSpace_nil]
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  omega

theorem binaryDiv2Code (number : Nat) :
    EvaluatorCodeFits Code.binaryDiv2Code [number]
      [number.div2] (binaryDiv2Cost number) where
  input_space := by
    simp [binaryDiv2Cost]
    omega
  output_space := by
    have quotientLe : number.div2 ≤ number := by
      have identity := Nat.bodd_add_div2 number
      omega
    have quotientBits := encodeNat_length_mono quotientLe
    simp only [binaryDiv2Cost, encodedListSpace_cons,
      encodedListSpace_nil]
    omega
  call continuation bound budget after := by
    let finalPayload :=
      [number.div2, number.bodd.toNat]
    have quotientLe : number.div2 ≤ number := by
      have identity := Nat.bodd_add_div2 number
      omega
    have quotientBits := encodeNat_length_mono quotientLe
    have parityLe : number.bodd.toNat ≤ 1 := by
      cases number.bodd <;> decide
    have parityBits := encodeNat_length_mono parityLe
    have oneBits :
        (Computability.encodeNat 1).length = 1 := rfl
    have finalSpace :
        encodedListSpace finalPayload ≤
          encodedListSpace [number] + 2 := by
      simp only [finalPayload, encodedListSpace_cons,
        encodedListSpace_nil]
      omega
    have finalLeCost :
        encodedListSpace finalPayload ≤
          binaryDiv2Cost number := by
      simp only [binaryDiv2Cost]
      omega
    have getFits :=
      get 0 finalPayload
    have getLeCost :
        getCost 0 finalPayload ≤
          binaryDiv2Cost number := by
      have localCost := getZeroCost_le finalPayload
      simp only [binaryDiv2Cost]
      omega
    have getBudget :
        getCost 0 finalPayload +
            continuationSpace continuation ≤
          bound := by
      omega
    have getCall :
        EvaluatorCallFits (Code.get 0) continuation
          finalPayload bound := by
      apply getFits.call continuation bound getBudget
      simpa [finalPayload] using after
    have afterFlat :
        EvaluatorExecutionFits bound
          (.ret (.comp (Code.get 0) continuation)
            finalPayload) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact getCall
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.binaryDiv2ListStepCode)
          (.comp (Code.get 0) continuation)
          [number, 0, 0] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := binaryDiv2BodyCost)
          (invariant := binaryDiv2Invariant number)
      · exact binaryDiv2Body
      · exact binaryDiv2Invariant_initial number
      · exact binaryDiv2Invariant_preserved number
      · intro remaining payload invariant
        have bodyCost :=
          binaryDiv2BodyCost_le_total
            number remaining payload invariant
        simp only [continuationSpace_comp]
        omega
      · simpa [finalPayload,
          Code.binaryDiv2ListStep_iterate] using afterFlat
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.binaryDiv2ListStepCode)
        (.comp (Code.get 0) continuation)
    have initialSpace :
        encodedListSpace [number, 0, 0] ≤
          binaryDiv2Cost number := by
      have zeroBits :
          (Computability.encodeNat 0).length = 0 := rfl
      simp only [binaryDiv2Cost, encodedListSpace_cons,
        encodedListSpace_nil, zeroBits]
      omega
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [number, 0, 0]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact flatCall
    have inputFits :=
      binaryDiv2InputCode [number]
    have inputLeCost :
        binaryDiv2InputCost [number] ≤
          binaryDiv2Cost number := by
      have inputCost := binaryDiv2InputCost_le [number]
      simp only [binaryDiv2Cost]
      omega
    have inputBudget :
        binaryDiv2InputCost [number] +
            continuationSpace loopContinuation ≤
          bound := by
      simp only [loopContinuation, continuationSpace_comp]
      omega
    have inputCall :
        EvaluatorCallFits Code.binaryDiv2InputCode
          loopContinuation [number] bound :=
      inputFits.call loopContinuation bound inputBudget afterInput
    have innerCall :=
      EvaluatorCallFits.comp inputCall
    have outerCall :=
      EvaluatorCallFits.comp innerCall
    simpa [Code.binaryDiv2Code, loopContinuation] using outerCall

end EvaluatorCodeFits

end PartrecToTM2
end Turing
