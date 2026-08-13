/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecBinaryLength
import LeanTrominoes.PartrecListCodeSpace
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

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

theorem encodeNat_length_le_of_lt_pow
    (number bits : Nat) (bounded : number < 2 ^ bits) :
    (Computability.encodeNat number).length ≤ bits := by
  rw [encodeNat_eq_bits, Nat.size_eq_bits_len, Nat.size_le]
  exact bounded

theorem encodeNat_eight_mul_add_four_length_le
    (number : Nat) :
    (Computability.encodeNat (8 * number + 4)).length ≤
      (Computability.encodeNat number).length + 3 := by
  let bits := (Computability.encodeNat number).length
  have numberPower :
      number < 2 ^ bits := by
    dsimp only [bits]
    rw [encodeNat_eq_bits, Nat.size_eq_bits_len]
    exact Nat.lt_size_self number
  have scaled :
      8 * number + 4 < 2 ^ (bits + 3) := by
    rw [pow_add]
    norm_num
    omega
  simpa [bits] using
    encodeNat_length_le_of_lt_pow
      (8 * number + 4) (bits + 3) scaled

theorem encodeNat_succ_length_le (number : Nat) :
    (Computability.encodeNat number.succ).length ≤
      (Computability.encodeNat number).length + 1 := by
  rw [encodeNat_eq_bits, encodeNat_eq_bits,
    Nat.size_eq_bits_len, Nat.size_eq_bits_len,
    Nat.size_le]
  have current := Nat.lt_size_self number
  rw [pow_succ]
  omega

/-- Binary length of a sum is bounded by the sum of the operand lengths plus
one carry bit. -/
theorem encodeNat_add_length_le_sum (left right : Nat) :
    (Computability.encodeNat (left + right)).length ≤
      (Computability.encodeNat left).length +
        (Computability.encodeNat right).length + 1 := by
  let leftBits := (Computability.encodeNat left).length
  let rightBits := (Computability.encodeNat right).length
  have leftPower : left < 2 ^ leftBits := by
    simpa [leftBits, encodeNat_eq_bits, Nat.size_eq_bits_len] using
      Nat.lt_size_self left
  have rightPower : right < 2 ^ rightBits := by
    simpa [rightBits, encodeNat_eq_bits, Nat.size_eq_bits_len] using
      Nat.lt_size_self right
  apply encodeNat_length_le_of_lt_pow
  have leftPowerPositive : 1 ≤ 2 ^ leftBits := one_le_pow₀ (by omega)
  have rightPowerPositive : 1 ≤ 2 ^ rightBits := one_le_pow₀ (by omega)
  rw [show leftBits + rightBits + 1 =
      (leftBits + rightBits) + 1 by omega,
    pow_add, pow_add]
  norm_num
  nlinarith

/-- Binary length of a product is at most the sum of the operand lengths. -/
theorem encodeNat_mul_length_le_sum (left right : Nat) :
    (Computability.encodeNat (left * right)).length ≤
      (Computability.encodeNat left).length +
        (Computability.encodeNat right).length := by
  by_cases leftZero : left = 0
  · subst left
    simp
  by_cases rightZero : right = 0
  · subst right
    simp
  let leftBits := (Computability.encodeNat left).length
  let rightBits := (Computability.encodeNat right).length
  have leftPower : left < 2 ^ leftBits := by
    simpa [leftBits, encodeNat_eq_bits, Nat.size_eq_bits_len] using
      Nat.lt_size_self left
  have rightPower : right < 2 ^ rightBits := by
    simpa [rightBits, encodeNat_eq_bits, Nat.size_eq_bits_len] using
      Nat.lt_size_self right
  have leftPositive : 0 < left := Nat.pos_of_ne_zero leftZero
  have rightPositive : 0 < right := Nat.pos_of_ne_zero rightZero
  apply encodeNat_length_le_of_lt_pow
  rw [pow_add]
  nlinarith

/-- Cantor-style natural pairing grows by only a constant factor in binary
length. -/
theorem encodeNat_pair_length_le (left right : Nat) :
    (Computability.encodeNat (Nat.pair left right)).length ≤
      3 * ((Computability.encodeNat left).length +
        (Computability.encodeNat right).length + 1) := by
  rw [Nat.pair]
  split_ifs with less
  · have square := encodeNat_mul_length_le_sum right right
    have total := encodeNat_add_length_le_sum (right * right) left
    omega
  · have square := encodeNat_mul_length_le_sum left left
    have firstSum := encodeNat_add_length_le_sum (left * left) left
    have total := encodeNat_add_length_le_sum (left * left + left) right
    omega

theorem encodeNat_length_le_self (number : Nat) :
    (Computability.encodeNat number).length ≤ number := by
  rw [encodeNat_eq_bits, Nat.size_eq_bits_len, Nat.size_le]
  exact number.lt_two_pow_self

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

theorem getOneCost_le (values : List Nat) :
    getCost 1 values ≤
      100000 * (encodedListSpace values + 1) := by
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
  have headSuccessorBits :=
    encodeNat_succ_length_le values.headI
  have tailSuccessorBits :=
    encodeNat_succ_length_le values.tail.headI
  have headPlusBits :
      (Computability.encodeNat (values.headI + 1)).length ≤
        (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using headSuccessorBits
  have tailPlusBits :
      (Computability.encodeNat
        (values.tail.headI + 1)).length ≤
          (Computability.encodeNat values.tail.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using tailSuccessorBits
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

def binaryLengthZeroBranchCost (values : List Nat) : Nat :=
  idCost values

def binaryLengthSuccBranchCost (values : List Nat) : Nat :=
  let remainingCost :=
    binaryDiv2Cost values.headI + getCost 0 values
  let countCost :=
    succCost [values.tail.headI] + getCost 1 values
  let restCost :=
    prependCost values [values.tail.headI.succ] []
      countCost (nilCost values)
  prependCost values [values.headI.div2]
    [values.tail.headI.succ] remainingCost restCost

def binaryLengthListStepCost (values : List Nat) : Nat :=
  if values.headI = 0 then
    branchZeroZeroCost values
      (Code.binaryLengthListStep values)
      values.headI (getCost 0 values)
      (binaryLengthZeroBranchCost values)
  else
    branchZeroSuccCost values
      (Code.binaryLengthListStep values)
      values.headI (getCost 0 values)
      (binaryLengthSuccBranchCost values)

theorem binaryLengthListStepCode (values : List Nat) :
    EvaluatorCodeFits Code.binaryLengthListStepCode values
      (Code.binaryLengthListStep values)
      (binaryLengthListStepCost values) := by
  have testFits :
      EvaluatorCodeFits (Code.get 0) values
        [values.headI] (getCost 0 values) := by
    simpa [getD_zero_eq_headI] using get 0 values
  by_cases remainingZero : values.headI = 0
  · simpa [Code.binaryLengthListStepCode,
      Code.binaryLengthListStep, binaryLengthListStepCost,
      binaryLengthZeroBranchCost, remainingZero] using
        branchZero_zero remainingZero testFits (id values)
  · have remainingField :=
      EvaluatorCodeFits.comp
        (binaryDiv2Code values.headI)
        (by
          simpa [getD_zero_eq_headI] using get 0 values)
    have countField :=
      EvaluatorCodeFits.comp
        (succ_named [values.tail.headI])
        (by
          simpa [getD_one_eq_tail_headI] using get 1 values)
    have rest :=
      prepend countField (nil values)
    have branch :=
      prepend remainingField rest
    simpa [Code.binaryLengthListStepCode,
      Code.binaryLengthListStep, binaryLengthListStepCost,
      binaryLengthSuccBranchCost, remainingZero,
      Code.prepend, prependCost] using
        branchZero_succ
          (Nat.pos_of_ne_zero remainingZero)
          testFits branch

theorem binaryLengthListStepCost_le (values : List Nat) :
    binaryLengthListStepCost values ≤
      1000000000 * (encodedListSpace values + 1) := by
  have headSpace :=
    encodedListSpace_singleton_headI_le values
  have tailHeadSpace :=
    encodedListSpace_singleton_tail_headI_le values
  have headBits :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have tailHeadBits :
      (Computability.encodeNat values.tail.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using tailHeadSpace
  have quotientLe : values.headI.div2 ≤ values.headI := by
    have identity := Nat.bodd_add_div2 values.headI
    omega
  have quotientBits := encodeNat_length_mono quotientLe
  have headSuccessorBits :=
    encodeNat_succ_length_le values.headI
  have headPlusBits :
      (Computability.encodeNat
        (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using headSuccessorBits
  have countSuccessorBits :=
    encodeNat_succ_length_le values.tail.headI
  have countPlusBits :
      (Computability.encodeNat
        (values.tail.headI + 1)).length ≤
          (Computability.encodeNat
            values.tail.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using countSuccessorBits
  have predecessorBits :=
    encodeNat_length_mono (Nat.pred_le values.headI)
  have predecessorBits' :
      (Computability.encodeNat
        (values.headI - 1)).length ≤
          (Computability.encodeNat values.headI).length := by
    simpa [Nat.pred_eq_sub_one] using predecessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have tailSpace := encodedListSpace_tail_le values
  by_cases remainingZero : values.headI = 0
  · rw [binaryLengthListStepCost, if_pos remainingZero]
    simp [branchZeroZeroCost, branchZeroTestCost,
      binaryLengthZeroBranchCost, prependCost,
      getCost, dropCost,
      idCost, headCost, nilCost, zeroPrimeCost,
      tailCost, succCost, Code.binaryLengthListStep,
      remainingZero, encodedListSpace_cons,
      encodedListSpace_nil, zeroBits]
    omega
  · rw [binaryLengthListStepCost, if_neg remainingZero]
    simp [branchZeroSuccCost, branchZeroTestCost,
      binaryLengthSuccBranchCost, prependCost, getCost,
      dropCost, idCost, headCost, nilCost,
      zeroPrimeCost, tailCost, succCost,
      binaryDiv2Cost, Code.binaryLengthListStep,
      remainingZero, encodedListSpace_cons,
      encodedListSpace_nil, zeroBits]
    omega

def binaryEncodingLengthInputCost (values : List Nat) : Nat :=
  let finalCost :=
    prependCost values [0] []
      (zeroCost values) (nilCost values)
  let remainingCost :=
    prependCost values [values.headI] [0]
      (getCost 0 values) finalCost
  prependCost values [values.headI] [values.headI, 0]
    (getCost 0 values) remainingCost

theorem binaryEncodingLengthInputCode (values : List Nat) :
    EvaluatorCodeFits Code.binaryEncodingLengthInputCode values
      [values.headI, values.headI, 0]
      (binaryEncodingLengthInputCost values) := by
  have final :=
    prepend (zero values) (nil values)
  have remaining :=
    prepend
      (by
        simpa [getD_zero_eq_headI] using get 0 values)
      final
  have fuel :=
    prepend
      (by
        simpa [getD_zero_eq_headI] using get 0 values)
      remaining
  simpa [Code.binaryEncodingLengthInputCode,
    binaryEncodingLengthInputCost, Code.prepend,
    prependCost] using fuel

theorem binaryEncodingLengthInputCost_le (values : List Nat) :
    binaryEncodingLengthInputCost values ≤
      1000000 * (encodedListSpace values + 1) := by
  have headSpace :=
    encodedListSpace_singleton_headI_le values
  have headBits :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have headSuccessorBits :=
    encodeNat_succ_length_le values.headI
  have headPlusBits :
      (Computability.encodeNat
        (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using headSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [binaryEncodingLengthInputCost, prependCost,
    getCost, dropCost, idCost, headCost, nilCost,
    zeroCost, zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits]
  omega

def binaryLengthBodyCost (remaining : Nat)
    (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.binaryLengthListStep
    binaryLengthListStepCost remaining payload

theorem binaryLengthBody
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.binaryLengthListStepCode)
      (remaining :: payload)
      (flatCountdownOutput Code.binaryLengthListStep
        remaining payload)
      (binaryLengthBodyCost remaining payload) := by
  simpa [binaryLengthBodyCost] using
    flatCountdownBody binaryLengthListStepCode
      remaining payload

theorem binaryLengthBodyCost_le
    (remaining : Nat) (payload : List Nat) :
    binaryLengthBodyCost remaining payload ≤
      100000000000 *
        (encodedListSpace (remaining :: payload) +
          encodedListSpace
            (Code.binaryLengthListStep payload) + 1) := by
  have stepCost := binaryLengthListStepCost_le payload
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
      simp [binaryLengthBodyCost, flatCountdownBodyCost,
        zeroPrimeCost, encodedListSpace_cons, zeroBits]
      omega
  | succ remaining =>
      rw [encodedListSpace_cons]
      have predecessorBits :
          (Computability.encodeNat remaining).length ≤
            (Computability.encodeNat (remaining + 1)).length :=
        encodeNat_length_mono (Nat.le_succ remaining)
      simp [binaryLengthBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, prependCost,
        idCost, headCost, nilCost, oneCost,
        zeroCost, zeroPrimeCost, tailCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits]
      omega

def binaryLengthInvariant (number remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = number ∧
      payload =
        (Code.binaryLengthListStep^[processed]) [number, 0]

theorem binaryLengthInvariant_initial (number : Nat) :
    binaryLengthInvariant number number [number, 0] := by
  exact ⟨0, by simp, rfl⟩

theorem binaryLengthInvariant_preserved
    (number remaining : Nat) (payload : List Nat)
    (invariant :
      binaryLengthInvariant number (remaining + 1) payload) :
    binaryLengthInvariant number remaining
      (Code.binaryLengthListStep payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']

def binaryEncodingLengthCost (number : Nat) : Nat :=
  10000000000000 * (encodedListSpace [number] + 1)

theorem binaryLengthBodyCost_le_total
    (number remaining : Nat) (payload : List Nat)
    (invariant :
      binaryLengthInvariant number remaining payload) :
    binaryLengthBodyCost remaining payload ≤
      binaryEncodingLengthCost number := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  let state :=
    (LeanTrominoes.Computability.binaryEncodingLengthStep^[
      processed]) (number, 0)
  let nextState :=
    (LeanTrominoes.Computability.binaryEncodingLengthStep^[
      processed + 1]) (number, 0)
  have remainingBound : remaining ≤ number := by omega
  have remainingBits :=
    encodeNat_length_mono remainingBound
  have stateInvariant :=
    LeanTrominoes.Computability.binaryEncodingLengthIterate_preserves
      processed (number, 0)
  have nextInvariant :=
    LeanTrominoes.Computability.binaryEncodingLengthIterate_preserves
      (processed + 1) (number, 0)
  have stateInvariant' :
      state.2 +
          (Computability.encodeNat state.1).length =
        (Computability.encodeNat number).length := by
    simpa [state] using stateInvariant
  have nextInvariant' :
      nextState.2 +
          (Computability.encodeNat nextState.1).length =
        (Computability.encodeNat number).length := by
    simpa [nextState] using nextInvariant
  have stateCountBits :
      (Computability.encodeNat state.2).length ≤
        (Computability.encodeNat number).length := by
    calc
      (Computability.encodeNat state.2).length ≤ state.2 :=
        encodeNat_length_le_self state.2
      _ ≤ (Computability.encodeNat number).length := by
        omega
  have nextCountBits :
      (Computability.encodeNat nextState.2).length ≤
        (Computability.encodeNat number).length := by
    calc
      (Computability.encodeNat nextState.2).length ≤
          nextState.2 :=
        encodeNat_length_le_self nextState.2
      _ ≤ (Computability.encodeNat number).length := by
        omega
  have currentList :=
    Code.binaryLengthListStep_iterate
      processed (number, 0)
  have nextList :=
    Code.binaryLengthListStep_iterate
      (processed + 1) (number, 0)
  have nextPayload :
      Code.binaryLengthListStep
          ((Code.binaryLengthListStep^[processed])
            [number, 0]) =
        (Code.binaryLengthListStep^[processed + 1])
          [number, 0] := by
    rw [Function.iterate_succ_apply']
  have bodyBound :=
    binaryLengthBodyCost_le remaining
      ((Code.binaryLengthListStep^[processed]) [number, 0])
  rw [nextPayload, currentList, nextList] at bodyBound
  rw [currentList]
  change
    binaryLengthBodyCost remaining [state.1, state.2] ≤
      100000000000 *
        (encodedListSpace
            (remaining :: [state.1, state.2]) +
          encodedListSpace [nextState.1, nextState.2] + 1) at bodyBound
  change
    binaryLengthBodyCost remaining [state.1, state.2] ≤
      binaryEncodingLengthCost number
  simp only [encodedListSpace_cons, encodedListSpace_nil] at bodyBound
  simp only [binaryEncodingLengthCost,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

theorem binaryLengthFinalList (number : Nat) :
    (Code.binaryLengthListStep^[number]) [number, 0] =
      [0,
        LeanTrominoes.Computability.binaryEncodingLength number] := by
  rw [Code.binaryLengthListStep_iterate number (number, 0)]
  have finished :=
    LeanTrominoes.Computability.binaryEncodingLengthIterate_fst_zero
      number number 0 (by rfl)
  change
    ((LeanTrominoes.Computability.binaryEncodingLengthStep^[
      number]) (number, 0)).1 = 0 at finished
  unfold LeanTrominoes.Computability.binaryEncodingLength
  rw [finished]

theorem binaryEncodingLengthCode (number : Nat) :
    EvaluatorCodeFits Code.binaryEncodingLengthCode [number]
      [LeanTrominoes.Computability.binaryEncodingLength number]
      (binaryEncodingLengthCost number) where
  input_space := by
    simp [binaryEncodingLengthCost]
    omega
  output_space := by
    have lengthBits :=
      encodeNat_length_le_self
        (LeanTrominoes.Computability.binaryEncodingLength number)
    rw [LeanTrominoes.Computability.binaryEncodingLength_eq] at lengthBits
    rw [LeanTrominoes.Computability.binaryEncodingLength_eq]
    simp only [binaryEncodingLengthCost,
      encodedListSpace_cons, encodedListSpace_nil]
    omega
  call continuation bound budget after := by
    let length :=
      LeanTrominoes.Computability.binaryEncodingLength number
    let finalPayload := [0, length]
    have lengthEq :
        length =
          (Computability.encodeNat number).length := by
      simp [length]
    have lengthBits :
        (Computability.encodeNat length).length ≤ length :=
      encodeNat_length_le_self length
    have zeroBits :
        (Computability.encodeNat 0).length = 0 := rfl
    rw [lengthEq] at lengthBits
    have finalSpace :
        encodedListSpace finalPayload ≤
          encodedListSpace [number] + 1 := by
      simp only [finalPayload, encodedListSpace_cons,
        encodedListSpace_nil, zeroBits]
      rw [lengthEq]
      omega
    have finalLeCost :
        encodedListSpace finalPayload ≤
          binaryEncodingLengthCost number := by
      simp only [binaryEncodingLengthCost]
      omega
    have getFits :=
      get 1 finalPayload
    have getLeCost :
        getCost 1 finalPayload ≤
          binaryEncodingLengthCost number := by
      have localCost := getOneCost_le finalPayload
      simp only [binaryEncodingLengthCost]
      omega
    have getCall :
        EvaluatorCallFits (Code.get 1) continuation
          finalPayload bound := by
      apply getFits.call continuation bound (by omega)
      simpa [finalPayload, length] using after
    have afterFlat :
        EvaluatorExecutionFits bound
          (.ret (.comp (Code.get 1) continuation)
            finalPayload) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact getCall
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.binaryLengthListStepCode)
          (.comp (Code.get 1) continuation)
          [number, number, 0] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := binaryLengthBodyCost)
          (invariant := binaryLengthInvariant number)
      · exact binaryLengthBody
      · exact binaryLengthInvariant_initial number
      · exact binaryLengthInvariant_preserved number
      · intro remaining payload invariant
        have bodyCost :=
          binaryLengthBodyCost_le_total
            number remaining payload invariant
        simp only [continuationSpace_comp]
        omega
      · simpa [finalPayload, length,
          binaryLengthFinalList] using afterFlat
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.binaryLengthListStepCode)
        (.comp (Code.get 1) continuation)
    have initialSpace :
        encodedListSpace [number, number, 0] ≤
          binaryEncodingLengthCost number := by
      have zeroBits :
          (Computability.encodeNat 0).length = 0 := rfl
      simp only [binaryEncodingLengthCost,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits]
      omega
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [number, number, 0]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact flatCall
    have inputFits :=
      binaryEncodingLengthInputCode [number]
    have inputLeCost :
        binaryEncodingLengthInputCost [number] ≤
          binaryEncodingLengthCost number := by
      have inputCost :=
        binaryEncodingLengthInputCost_le [number]
      simp only [binaryEncodingLengthCost]
      omega
    have inputCall :
        EvaluatorCallFits Code.binaryEncodingLengthInputCode
          loopContinuation [number] bound :=
      inputFits.call loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp]
          omega)
        afterInput
    have innerCall :=
      EvaluatorCallFits.comp inputCall
    have outerCall :=
      EvaluatorCallFits.comp innerCall
    simpa [Code.binaryEncodingLengthCode,
      loopContinuation] using outerCall

theorem encodeNat_add_length_le (number increment : Nat) :
    (Computability.encodeNat (number + increment)).length ≤
      (Computability.encodeNat number).length + increment := by
  induction increment with
  | zero =>
      simp
  | succ increment induction =>
      rw [Nat.add_succ]
      exact
        (encodeNat_succ_length_le (number + increment)).trans
          (by omega)

theorem headCost_le (values : List Nat) :
    headCost values ≤
      1000 * (encodedListSpace values + 1) := by
  have headSpace :=
    encodedListSpace_singleton_headI_le values
  have headBits :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits :=
    encodeNat_succ_length_le values.headI
  have headPlusBits :
      (Computability.encodeNat
        (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [headCost, idCost, nilCost, zeroPrimeCost,
    tailCost, succCost, encodedListSpace_cons,
    encodedListSpace_nil, zeroBits]
  omega

theorem succCost_le (values : List Nat) :
    succCost values ≤
      100 * (encodedListSpace values + 1) := by
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
  simp [succCost]
  omega

theorem addConstCost_le (increment : Nat)
    (values : List Nat) :
    addConstCost increment values ≤
      1000 * (increment + 1) *
        (encodedListSpace values + increment + 1) := by
  induction increment with
  | zero =>
      simp only [addConstCost, Nat.zero_add]
      have cost := headCost_le values
      omega
  | succ increment induction =>
      simp only [addConstCost]
      have intermediateBits :=
        encodeNat_add_length_le values.headI increment
      have headBits :
          (Computability.encodeNat values.headI).length ≤
            encodedListSpace values := by
        have headSpace :=
          encodedListSpace_singleton_headI_le values
        simpa [encodedListSpace_cons] using headSpace
      have intermediateSpace :
          encodedListSpace [values.headI + increment] ≤
            encodedListSpace values + increment + 1 := by
        simp only [encodedListSpace_cons,
          encodedListSpace_nil]
        omega
      have nextCost :=
        succCost_le [values.headI + increment]
      nlinarith

def binaryLengthAffineInput22Cost (number : Nat) : Nat :=
  let values := [number]
  let length :=
    LeanTrominoes.Computability.binaryEncodingLength number
  let restCost :=
    prependCost values [22] []
      (numeralCost 22 values) (nilCost values)
  prependCost values [length] [22]
    (binaryEncodingLengthCost number) restCost

theorem binaryLengthAffineInput22Code (number : Nat) :
    EvaluatorCodeFits (Code.binaryLengthAffineInputCode 22)
      [number]
      [LeanTrominoes.Computability.binaryEncodingLength number, 22]
      (binaryLengthAffineInput22Cost number) := by
  have rest :=
    prepend (numeral 22 [number]) (nil [number])
  have result :=
    prepend (binaryEncodingLengthCode number) rest
  simpa [Code.binaryLengthAffineInputCode,
    binaryLengthAffineInput22Cost, Code.prepend,
    prependCost] using result

def binaryLengthAffine21Cost (number : Nat) : Nat :=
  1000000000000000 * (encodedListSpace [number] + 1)

theorem binaryLengthAffineInput22Cost_le (number : Nat) :
    binaryLengthAffineInput22Cost number ≤
      binaryLengthAffine21Cost number := by
  let length :=
    LeanTrominoes.Computability.binaryEncodingLength number
  have lengthEq :
      length = (Computability.encodeNat number).length := by
    simp [length]
  have lengthBits :
      (Computability.encodeNat length).length ≤ length :=
    encodeNat_length_le_self length
  rw [lengthEq] at lengthBits
  have numeralCostBound :=
    addConstCost_le 22 [0]
  have headBits :
      (Computability.encodeNat number).length ≤
        encodedListSpace [number] := by
    simp [encodedListSpace_cons]
  have numberSuccessorBits :=
    encodeNat_succ_length_le number
  have numberPlusBits :
      (Computability.encodeNat (number + 1)).length ≤
        (Computability.encodeNat number).length + 1 := by
    simpa [Nat.succ_eq_add_one] using numberSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have bits22 :
      (Computability.encodeNat 22).length ≤ 22 :=
    encodeNat_length_le_self 22
  simp [binaryLengthAffineInput22Cost,
    binaryLengthAffine21Cost, binaryEncodingLengthCost,
    prependCost, numeralCost,
    zeroCost, nilCost,
    zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    length, zeroBits] at *
  omega

def binaryLengthAffine21BodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost (Code.addConstListStep 21)
    (addConstCost 21) remaining payload

theorem binaryLengthAffine21Body
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.addConst 21))
      (remaining :: payload)
      (flatCountdownOutput (Code.addConstListStep 21)
        remaining payload)
      (binaryLengthAffine21BodyCost remaining payload) := by
  have stepEq :
      Code.addConstListStep 21 =
        fun values => [values.headI + 21] := by
    rfl
  rw [stepEq]
  simpa [binaryLengthAffine21BodyCost, stepEq] using
    flatCountdownBody (addConst 21)
      remaining payload

theorem binaryLengthAffine21BodyCost_le
    (remaining : Nat) (payload : List Nat) :
    binaryLengthAffine21BodyCost remaining payload ≤
      1000000000 *
        (encodedListSpace (remaining :: payload) +
          encodedListSpace
            (Code.addConstListStep 21 payload) + 22) := by
  have stepCost := addConstCost_le 21 payload
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
      simp [binaryLengthAffine21BodyCost,
        flatCountdownBodyCost, zeroPrimeCost,
        encodedListSpace_cons, zeroBits]
      omega
  | succ remaining =>
      rw [encodedListSpace_cons]
      have predecessorBits :
          (Computability.encodeNat remaining).length ≤
            (Computability.encodeNat (remaining + 1)).length :=
        encodeNat_length_mono (Nat.le_succ remaining)
      simp [binaryLengthAffine21BodyCost,
        flatCountdownBodyCost, flatCountdownSuccBranchCost,
        prependCost, idCost, headCost, nilCost, oneCost,
        zeroCost, zeroPrimeCost, tailCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits]
      omega

def binaryLengthAffine21Invariant
    (steps remaining : Nat) (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = steps ∧
      payload =
        ((Code.addConstListStep 21)^[processed]) [22]

theorem binaryLengthAffine21Invariant_initial (steps : Nat) :
    binaryLengthAffine21Invariant steps steps [22] := by
  exact ⟨0, by simp, rfl⟩

theorem binaryLengthAffine21Invariant_preserved
    (steps remaining : Nat) (payload : List Nat)
    (invariant :
      binaryLengthAffine21Invariant steps (remaining + 1)
        payload) :
    binaryLengthAffine21Invariant steps remaining
      (Code.addConstListStep 21 payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']

theorem binaryLengthAffine21BodyCost_le_total
    (number remaining : Nat) (payload : List Nat)
    (invariant :
      binaryLengthAffine21Invariant
        (LeanTrominoes.Computability.binaryEncodingLength number)
        remaining payload) :
    binaryLengthAffine21BodyCost remaining payload ≤
      binaryLengthAffine21Cost number := by
  let length :=
    LeanTrominoes.Computability.binaryEncodingLength number
  obtain ⟨processed, sum, rfl⟩ := invariant
  have lengthEq :
      length = (Computability.encodeNat number).length := by
    simp [length]
  have remainingBound : remaining ≤ length := by
    simpa [length] using
      (show remaining ≤
          LeanTrominoes.Computability.binaryEncodingLength number by
        omega)
  have remainingBitsToLength :=
    encodeNat_length_mono remainingBound
  have lengthBits :
      (Computability.encodeNat length).length ≤ length :=
    encodeNat_length_le_self length
  have remainingBits :
      (Computability.encodeNat remaining).length ≤ length :=
    remainingBitsToLength.trans lengthBits
  have processedBound : processed ≤ length := by
    simpa [length] using
      (show processed ≤
          LeanTrominoes.Computability.binaryEncodingLength number by
        omega)
  have nextBound : processed + 1 ≤ length + 1 := by omega
  have valueBits :
      (Computability.encodeNat
        (22 + processed * 21)).length ≤
          22 + processed * 21 :=
    encodeNat_length_le_self _
  have nextValueBits :
      (Computability.encodeNat
        (22 + (processed + 1) * 21)).length ≤
          22 + (processed + 1) * 21 :=
    encodeNat_length_le_self _
  have currentList :=
    Code.addConstListStep_iterate 21 processed 22
  have nextList :=
    Code.addConstListStep_iterate 21 (processed + 1) 22
  have nextPayload :
      Code.addConstListStep 21
          (((Code.addConstListStep 21)^[processed]) [22]) =
        ((Code.addConstListStep 21)^[processed + 1]) [22] := by
    rw [Function.iterate_succ_apply']
  have bodyBound :=
    binaryLengthAffine21BodyCost_le remaining
      (((Code.addConstListStep 21)^[processed]) [22])
  rw [nextPayload, currentList, nextList] at bodyBound
  rw [currentList]
  simp only [encodedListSpace_cons, encodedListSpace_nil] at bodyBound
  simp only [binaryLengthAffine21Cost,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

theorem binaryLengthAffine21Code (number : Nat) :
    EvaluatorCodeFits (Code.binaryLengthAffineCode 21 22)
      [number]
      [22 + 21 *
        LeanTrominoes.Computability.binaryEncodingLength number]
      (binaryLengthAffine21Cost number) where
  input_space := by
    simp [binaryLengthAffine21Cost]
    omega
  output_space := by
    let length :=
      LeanTrominoes.Computability.binaryEncodingLength number
    have lengthEq :
        length = (Computability.encodeNat number).length := by
      simp [length]
    have resultBits :=
      encodeNat_length_le_self (22 + 21 * length)
    change
      encodedListSpace [22 + 21 * length] ≤
        binaryLengthAffine21Cost number
    simp only [binaryLengthAffine21Cost,
      encodedListSpace_cons, encodedListSpace_nil]
    omega
  call continuation bound budget after := by
    let length :=
      LeanTrominoes.Computability.binaryEncodingLength number
    have lengthEq :
        length = (Computability.encodeNat number).length := by
      simp [length]
    have finalList :
        ((Code.addConstListStep 21)^[length]) [22] =
          [22 + 21 * length] := by
      rw [Code.addConstListStep_iterate]
      congr 1
      omega
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate (Code.addConst 21))
          continuation [length, 22] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := binaryLengthAffine21BodyCost)
          (invariant :=
            binaryLengthAffine21Invariant length)
      · exact binaryLengthAffine21Body
      · exact binaryLengthAffine21Invariant_initial length
      · exact binaryLengthAffine21Invariant_preserved length
      · intro remaining payload invariant
        have bodyCost :=
          binaryLengthAffine21BodyCost_le_total
            number remaining payload (by
              simpa [length] using invariant)
        omega
      · rw [finalList]
        simpa [length] using after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate (Code.addConst 21)) continuation
    have initialSpace :
        encodedListSpace [length, 22] ≤
          binaryLengthAffine21Cost number := by
      have lengthBits :
          (Computability.encodeNat length).length ≤ length :=
        encodeNat_length_le_self length
      have bits22 :
          (Computability.encodeNat 22).length ≤ 22 :=
        encodeNat_length_le_self 22
      simp only [binaryLengthAffine21Cost,
        encodedListSpace_cons, encodedListSpace_nil]
      omega
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [length, 22]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        omega
      · exact flatCall
    have inputFits :=
      binaryLengthAffineInput22Code number
    have inputCost :=
      binaryLengthAffineInput22Cost_le number
    have inputCall :
        EvaluatorCallFits
          (Code.binaryLengthAffineInputCode 22)
          loopContinuation [number] bound :=
      inputFits.call loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp]
          omega)
        (by simpa [length] using afterInput)
    simpa [Code.binaryLengthAffineCode,
      loopContinuation] using
        EvaluatorCallFits.comp inputCall

end EvaluatorCodeFits

end PartrecToTM2
end Turing
