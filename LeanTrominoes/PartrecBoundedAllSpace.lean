/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedAll
import LeanTrominoes.PartrecBooleanSpace

/-! # Space certificates for uniform bounded conjunction loops -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec

/-- Exact compositional allowance for one conjunction step. -/
def boundedAllStepCost (payload : List Nat) (valid value : Bool) (index leafCost : Nat) : Nat :=
  let values := valid.toNat :: index :: payload
  let updated := boolAndCost values valid.toNat value.toNat
    (getCost 0 values) (leafCost + tailCost values)
  let advanced := succCost [index] + getCost 1 values
  prependCost values [(valid && value).toNat] ((index+1) :: payload) updated
    (prependCost values [index+1] payload advanced (dropCost 2 values))

theorem boundedAllStep {leaf : Code} (payload : List Nat) (valid value : Bool)
    (index leafCost : Nat)
    (leafFit : EvaluatorCodeFits leaf (index :: payload) [value.toNat] leafCost) :
    EvaluatorCodeFits (Code.boundedAllStep leaf) (valid.toNat :: index :: payload)
      ((valid && value).toNat :: (index+1) :: payload)
      (boundedAllStepCost payload valid value index leafCost) := by
  let values := valid.toNat :: index :: payload
  have leafCall := comp leafFit (tail_named values)
  have accumulator : EvaluatorCodeFits (Code.get 0) values [valid.toNat] (getCost 0 values) := by
    simpa [values] using get 0 values
  have combined := boolAnd accumulator leafCall
  have updated : EvaluatorCodeFits (Code.boolAnd (Code.get 0) (leaf.comp Code.tail)) values
      [(valid && value).toNat]
      (boolAndCost values valid.toNat value.toNat (getCost 0 values) (leafCost+tailCost values)) := by
    cases valid <;> cases value <;> simpa using combined
  have advanced := comp (succ_named [index]) (get 1 values)
  have output := prepend updated (prepend advanced (drop 2 values))
  simpa [Code.boundedAllStep,boundedAllStepCost,values] using output

def boundedAllBodyCost (payload : List Nat) (valid value : Bool) (index remaining leafCost : Nat) : Nat :=
  flatCountdownBodyCost (fun _ => (valid && value).toNat :: (index+1) :: payload)
    (fun _ => boundedAllStepCost payload valid value index leafCost)
    remaining (valid.toNat :: index :: payload)

theorem boundedAllBody {leaf : Code} (payload : List Nat) (valid value : Bool)
    (index remaining leafCost : Nat)
    (leafFit : EvaluatorCodeFits leaf (index :: payload) [value.toNat] leafCost) :
    EvaluatorCodeFits (Code.flatCountdownBody (Code.boundedAllStep leaf))
      (remaining :: valid.toNat :: index :: payload)
      (if remaining = 0 then 0 :: valid.toNat :: index :: payload
       else 1 :: (remaining-1) :: (valid && value).toNat :: (index+1) :: payload)
      (boundedAllBodyCost payload valid value index remaining leafCost) := by
  have body := flatCountdownBody_of_fit (boundedAllStep payload valid value index leafCost leafFit) remaining
  cases remaining <;> simpa [boundedAllBodyCost,flatCountdownOutput] using body

/-- The uniform body allowance includes no factor for the number of iterations. -/
theorem boundedAllIterate {leaf : Code} (payload : List Nat) (predicate : Nat → Bool)
    (limit budget : Nat) (leafCost : Nat → Nat)
    (leafFits : ∀ i, i ≤ limit → EvaluatorCodeFits leaf (i :: payload) [(predicate i).toNat] (leafCost i))
    (bodyBudget : ∀ remaining index valid, index+remaining ≤ limit →
      boundedAllBodyCost payload valid (predicate index) index remaining (leafCost index) ≤ budget)
    (count start : Nat) (valid : Bool) (within : start+count ≤ limit) :
    EvaluatorCodeFits (Code.flatIterate (Code.boundedAllStep leaf))
      (count :: valid.toNat :: start :: payload)
      ((valid && Code.allFrom predicate start count).toNat :: (start+count) :: payload)
      budget := by
  have bodyFits (remaining index : Nat) (acc : Bool) (h : index+remaining ≤ limit) :=
    (boundedAllBody payload acc (predicate index) index remaining (leafCost index)
      (leafFits index (by omega))).mono (bodyBudget remaining index acc h)
  constructor
  · exact (bodyFits count start valid within).input_space
  · have finalFit := bodyFits 0 (start+count) (valid && Code.allFrom predicate start count) (by omega)
    have finalSpace := finalFit.input_space
    simp only [encodedListSpace_cons] at finalSpace ⊢
    omega
  · intro continuation bound allowed after
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction count generalizing start valid with
    | zero =>
      have fit := bodyFits 0 start valid within
      apply fit.call (.fix (Code.flatCountdownBody (Code.boundedAllStep leaf)) continuation) bound
      · simpa using allowed
      · apply EvaluatorExecutionFits.ret_fix_zero
        · rfl
        · simpa using (Nat.add_le_add_right fit.output_space (continuationSpace continuation)).trans allowed
        · simpa [Code.allFrom] using after
    | succ count ih =>
      have fit := bodyFits (count+1) start valid within
      have next : start+1+count ≤ limit := by omega
      have recursiveAfter : EvaluatorExecutionFits bound
          (.ret continuation (((valid && predicate start) && Code.allFrom predicate (start+1) count).toNat ::
            (start+1+count) :: payload)) := by
        simpa [Code.allFrom,Bool.and_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using after
      have recursive := ih (start+1) (valid && predicate start) next recursiveAfter
      apply fit.call (.fix (Code.flatCountdownBody (Code.boundedAllStep leaf)) continuation) bound
      · simpa using allowed
      · apply EvaluatorExecutionFits.ret_fix_succ
        · simp
        · simpa using (Nat.add_le_add_right fit.output_space (continuationSpace continuation)).trans allowed
        · simpa using recursive

/-- A linear envelope in the retained data, index bits, and leaf workspace. -/
def boundedAllBudget (payload : List Nat) (bits leafBudget : Nat) : Nat :=
  1000000 * (encodedListSpace payload + bits + leafBudget + 1)

set_option maxHeartbeats 800000 in
theorem boundedAllBodyCost_le (payload : List Nat) (valid value : Bool)
    (index remaining bits leafCost leafBudget : Nat)
    (indexBits : (Computability.encodeNat index).length ≤ bits)
    (remainingBits : (Computability.encodeNat remaining).length ≤ bits)
    (leafBound : leafCost ≤ leafBudget) :
    boundedAllBodyCost payload valid value index remaining leafCost ≤
      boundedAllBudget payload bits leafBudget := by
  have nextBits := listCodeEncodeNat_succ_length_le index
  have headSpace := listCodeEncodedListSpace_singleton_headI_le payload
  have headNext := listCodeEncodeNat_succ_length_le payload.headI
  simp only [Nat.succ_eq_add_one] at nextBits headNext
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have twoBits : (Computability.encodeNat 2).length = 2 := by decide
  simp only [encodedListSpace_cons,encodedListSpace_nil] at headSpace
  cases remaining with
  | zero =>
    cases valid <;> cases value <;>
      simp [boundedAllBodyCost,flatCountdownBodyCost,zeroPrimeCost,boundedAllBudget,
        encodedListSpace_cons,encodedListSpace_nil,zeroBits,oneBits] <;> omega
  | succ remaining =>
    have previousBits := listCodeEncodeNat_length_mono (Nat.le_succ remaining)
    simp only [Nat.succ_eq_add_one] at previousBits
    cases valid <;> cases value <;>
      simp [boundedAllBodyCost,flatCountdownBodyCost,flatCountdownSuccBranchCost,
        boundedAllStepCost,boolAndCost,normalizeBoolCost,branchZeroZeroCost,branchZeroSuccCost,
        branchZeroTestCost,prependCost,getCost,dropCost,headCost,idCost,nilCost,
        zeroCost,oneCost,tailCost,zeroPrimeCost,succCost,boundedAllBudget,
        encodedListSpace_cons,encodedListSpace_nil,zeroBits,oneBits,twoBits] <;> omega

/-- A complete iteration certificate from a bound on index bits and the leaf. -/
theorem boundedAllIterate_uniform {leaf : Code} (payload : List Nat) (predicate : Nat → Bool)
    (count bits leafBudget : Nat)
    (countBits : (Computability.encodeNat count).length ≤ bits)
    (leafFits : ∀ i, i ≤ count → EvaluatorCodeFits leaf (i :: payload) [(predicate i).toNat] leafBudget) :
    EvaluatorCodeFits (Code.flatIterate (Code.boundedAllStep leaf))
      (count :: 1 :: 0 :: payload)
      ((Code.allFrom predicate 0 count).toNat :: count :: payload)
      (boundedAllBudget payload bits leafBudget) := by
  have result := boundedAllIterate payload predicate count (boundedAllBudget payload bits leafBudget)
    (fun _ => leafBudget) leafFits
    (fun remaining index valid h => boundedAllBodyCost_le payload valid (predicate index)
      index remaining bits leafBudget leafBudget
      ((listCodeEncodeNat_length_mono (by omega : index ≤ count)).trans countBits)
      ((listCodeEncodeNat_length_mono (by omega : remaining ≤ count)).trans countBits) (by rfl))
    count 0 true (by omega)
  simpa using result

def boundedAllInputCost (payload : List Nat) (count : Nat) : Nat :=
  let values := count :: payload
  prependCost values [count] (1 :: 0 :: payload) (getCost 0 values)
    (prependCost values [1] (0 :: payload) (oneCost values)
      (zeroPrimeCost payload + tailCost values))

theorem boundedAllInput (payload : List Nat) (count : Nat) :
    EvaluatorCodeFits Code.boundedAllInput (count :: payload) (count :: 1 :: 0 :: payload)
      (boundedAllInputCost payload count) := by
  have rest := comp (zero'_named payload) (tail_named (count :: payload))
  have result := prepend (get 0 (count :: payload)) (prepend (one (count :: payload)) rest)
  simpa [Code.boundedAllInput,boundedAllInputCost] using result

def boundedAllCost (payload : List Nat) (count bits leafBudget : Nat) (result : Bool) : Nat :=
  getCost 0 (result.toNat :: count :: payload) + boundedAllBudget payload bits leafBudget +
    boundedAllInputCost payload count

/-- Complete bounded-quantifier code, including initialization and result projection. -/
theorem boundedAll {leaf : Code} (payload : List Nat) (predicate : Nat → Bool)
    (count bits leafBudget : Nat)
    (countBits : (Computability.encodeNat count).length ≤ bits)
    (leafFits : ∀ i, i ≤ count → EvaluatorCodeFits leaf (i :: payload) [(predicate i).toNat] leafBudget) :
    EvaluatorCodeFits (Code.boundedAll leaf) (count :: payload)
      [(Code.allFrom predicate 0 count).toNat]
      (boundedAllCost payload count bits leafBudget (Code.allFrom predicate 0 count)) := by
  have loop := boundedAllIterate_uniform payload predicate count bits leafBudget countBits leafFits
  have whole := comp (get 0 ((Code.allFrom predicate 0 count).toNat :: count :: payload))
    (comp loop (boundedAllInput payload count))
  simpa [Code.boundedAll,boundedAllCost,Nat.add_assoc] using whole

set_option maxHeartbeats 400000 in
theorem boundedAllCost_le (payload : List Nat) (count bits leafBudget : Nat) (result : Bool)
    (countBits : (Computability.encodeNat count).length ≤ bits) :
    boundedAllCost payload count bits leafBudget result ≤
      10000000 * (encodedListSpace payload + bits + leafBudget + 1) := by
  have nextBits := listCodeEncodeNat_succ_length_le count
  simp only [Nat.succ_eq_add_one] at nextBits
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have twoBits : (Computability.encodeNat 2).length = 2 := by decide
  cases result <;>
    simp [boundedAllCost,boundedAllInputCost,boundedAllBudget,prependCost,getCost,dropCost,
      headCost,idCost,nilCost,zeroCost,oneCost,tailCost,zeroPrimeCost,succCost,
      encodedListSpace_cons,encodedListSpace_nil,zeroBits,oneBits,twoBits] <;> omega

theorem boundedAll_uniform {leaf : Code} (payload : List Nat) (predicate : Nat → Bool)
    (count bits leafBudget : Nat)
    (countBits : (Computability.encodeNat count).length ≤ bits)
    (leafFits : ∀ i, i ≤ count → EvaluatorCodeFits leaf (i :: payload) [(predicate i).toNat] leafBudget) :
    EvaluatorCodeFits (Code.boundedAll leaf) (count :: payload)
      [(Code.allFrom predicate 0 count).toNat]
      (10000000 * (encodedListSpace payload + bits + leafBudget + 1)) :=
  (boundedAll payload predicate count bits leafBudget countBits leafFits).mono
    (boundedAllCost_le payload count bits leafBudget _ countBits)

end Turing.PartrecToTM2.EvaluatorCodeFits
