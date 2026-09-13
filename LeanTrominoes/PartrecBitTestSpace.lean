/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBitTest
import LeanTrominoes.PartrecBoundedArithmeticCombinatorsSpace

/-! # Binary-space bounds for bit lookup at an arbitrary natural index -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec
open LeanTrominoes.BoundedArithmetic

def shiftWordBudget (bits : Nat) : Nat := 10000000000*(bits+1)

def shiftWordBodyCost (word remaining : Nat) : Nat :=
  flatCountdownBodyCost (fun _ => [word.div2]) (fun _ => binaryDiv2Cost word) remaining [word]

set_option maxHeartbeats 400000 in
theorem shiftWordBodyCost_le (word remaining bits : Nat)
    (hw : (Computability.encodeNat word).length ≤ bits)
    (hr : (Computability.encodeNat remaining).length ≤ bits) :
    shiftWordBodyCost word remaining ≤ shiftWordBudget bits := by
  have hd := (listCodeEncodeNat_length_mono (show word.div2 ≤ word by simp [Nat.div2_val]; omega)).trans hw
  have hwn := listCodeEncodeNat_succ_length_le word
  have h0 : (Computability.encodeNat 0).length = 0 := rfl
  have h1 : (Computability.encodeNat 1).length = 1 := rfl
  simp only [Nat.succ_eq_add_one] at hwn
  cases remaining with
  | zero =>
    simp [shiftWordBodyCost,flatCountdownBodyCost,zeroPrimeCost,shiftWordBudget,
      encodedListSpace_cons,encodedListSpace_nil,h0]
    omega
  | succ remaining =>
    have hp := listCodeEncodeNat_length_mono (Nat.le_succ remaining)
    have hnext := listCodeEncodeNat_succ_length_le remaining
    simp only [Nat.succ_eq_add_one] at hp hnext
    simp [shiftWordBodyCost,flatCountdownBodyCost,flatCountdownSuccBranchCost,binaryDiv2Cost,
      prependCost,headCost,idCost,nilCost,zeroCost,oneCost,tailCost,zeroPrimeCost,succCost,
      shiftWordBudget,encodedListSpace_cons,encodedListSpace_nil,h0,h1]
    omega

theorem shiftWordBody (word remaining bits : Nat)
    (hw : (Computability.encodeNat word).length ≤ bits)
    (hr : (Computability.encodeNat remaining).length ≤ bits) :
    EvaluatorCodeFits (Code.flatCountdownBody Code.binaryDiv2Code) [remaining,word]
      (if remaining = 0 then [0,word] else [1,remaining-1,word.div2]) (shiftWordBudget bits) := by
  have body := (flatCountdownBody_of_fit (binaryDiv2Code word) remaining).mono
    (shiftWordBodyCost_le word remaining bits hw hr)
  cases remaining <;> simpa [flatCountdownOutput] using body

/-- Repeated halving reuses a single workspace budget, even for very large indices. -/
theorem shiftWord (word index bits : Nat)
    (hw : (Computability.encodeNat word).length ≤ bits)
    (hi : (Computability.encodeNat index).length ≤ bits) :
    EvaluatorCodeFits (Code.flatIterate Code.binaryDiv2Code) [index,word]
      [Code.shiftedWord word index] (shiftWordBudget bits) := by
  have resultBits := (listCodeEncodeNat_length_mono (Code.shiftedWord_le word index)).trans hw
  constructor
  · simp [encodedListSpace_cons,encodedListSpace_nil,shiftWordBudget]; omega
  · simp [encodedListSpace_cons,encodedListSpace_nil,shiftWordBudget]; omega
  · intro continuation bound allowed after
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction index generalizing word with
    | zero =>
      have fit := shiftWordBody word 0 bits hw hi
      apply fit.call (.fix (Code.flatCountdownBody Code.binaryDiv2Code) continuation) bound
      · simpa using allowed
      · apply EvaluatorExecutionFits.ret_fix_zero
        · rfl
        · simpa using (Nat.add_le_add_right fit.output_space (continuationSpace continuation)).trans allowed
        · simpa [Code.shiftedWord] using after
    | succ index ih =>
      have hp := (listCodeEncodeNat_length_mono (Nat.le_succ index)).trans hi
      have hd := (listCodeEncodeNat_length_mono (show word.div2 ≤ word by simp [Nat.div2_val]; omega)).trans hw
      have hr := (listCodeEncodeNat_length_mono (Code.shiftedWord_le word.div2 index)).trans hd
      have recursiveAfter : EvaluatorExecutionFits bound
          (.ret continuation [Code.shiftedWord word.div2 index]) := by
        simpa [Code.shiftedWord,Function.iterate_succ_apply] using after
      have recursive := ih word.div2 hd hp hr recursiveAfter
      have fit := shiftWordBody word (index+1) bits hw hi
      apply fit.call (.fix (Code.flatCountdownBody Code.binaryDiv2Code) continuation) bound
      · simpa using allowed
      · apply EvaluatorExecutionFits.ret_fix_succ
        · simp
        · simpa using (Nat.add_le_add_right fit.output_space (continuationSpace continuation)).trans allowed
        · simpa using recursive

def parityBudget (bits : Nat) : Nat := 1000000000000000*(bits+1)

theorem parity (word bits : Nat) (hw : (Computability.encodeNat word).length ≤ bits) :
    EvaluatorCodeFits Code.parityCode [word] [(word.testBit 0).toNat] (parityBudget bits) := by
  let argsCost := prependCost [word] [word] [2] (headCost [word]) (numeralCost 2 [word])
  let projection := getCost 1 [word/2,word%2]
  have arguments := prepend (head [word]) (numeral 2 [word])
  have fitted := comp (get 1 [word/2,word%2]) (comp (division word 2) arguments)
  have h2 : (Computability.encodeNat 2).length = 2 := by decide
  have h8 : (Computability.encodeNat 8).length = 4 := by decide
  have h16 : (Computability.encodeNat 16).length = 5 := by decide
  have hs := encodeNat_add_length_le_sum word 2
  have hm := encodeNat_mul_length_le_sum 8 (word+2)
  have ht := encodeNat_add_length_le_sum (8*(word+2)) 16
  rw [h2] at hs
  rw [h8] at hm
  rw [h16] at ht
  have hhead := headCost_bound [word]
  have hz := listCodeZeroCost_le_linear [word]
  have hc : addConstCost 2 [0] ≤ 100 := by decide
  have hargs : argsCost ≤ 100000*(bits+1) := by
    simp only [argsCost,prependCost,numeralCost,encodedListSpace_cons,encodedListSpace_nil,
      List.headI_cons,h2] at *
    omega
  have hq := (listCodeEncodeNat_length_mono (Nat.div_le_self word 2)).trans hw
  have hr := (listCodeEncodeNat_length_mono (Nat.mod_le word 2)).trans hw
  have hp := listCodeGetCost_le_linear 1 [word/2,word%2]
  have hprojection : projection ≤ 100000*(bits+1) := by
    simp only [projection,encodedListSpace_cons,encodedListSpace_nil] at *
    omega
  have cost : projection+(divisionSpaceBound word 2+argsCost) ≤ parityBudget bits := by
    simp only [divisionSpaceBound,encodedListSpace_cons,encodedListSpace_nil,parityBudget]
    omega
  have result : word%2 = (word.testBit 0).toNat := by
    have h : word%2 = 0 ∨ word%2 = 1 := by omega
    rcases h with h | h <;> simp [Nat.testBit_zero,h]
  have whole := fitted.mono cost
  change EvaluatorCodeFits Code.parityCode [word] [word%2] (parityBudget bits) at whole
  rw [result] at whole
  exact whole

def bitTestBudget (bits : Nat) : Nat := 100000000000000000000*(bits+1)

theorem bitTest (word index bits : Nat)
    (hw : (Computability.encodeNat word).length ≤ bits)
    (hi : (Computability.encodeNat index).length ≤ bits) :
    EvaluatorCodeFits Code.bitTestCode [word,index] [(word.testBit index).toNat] (bitTestBudget bits) := by
  have shifted := shiftWord word index bits hw hi
  have resultBits := (listCodeEncodeNat_length_mono (Code.shiftedWord_le word index)).trans hw
  have args := prepend (get 1 [word,index]) (get 0 [word,index])
  have fit := comp (parity (Code.shiftedWord word index) bits resultBits) (comp shifted args)
  have first := listCodeGetCost_le_linear 1 [word,index]
  have second := listCodeGetCost_le_linear 0 [word,index]
  have cost : parityBudget bits + (shiftWordBudget bits +
      prependCost [word,index] [index] [word] (getCost 1 [word,index]) (getCost 0 [word,index])) ≤
      bitTestBudget bits := by
    simp only [encodedListSpace_cons,encodedListSpace_nil] at first second
    simp [parityBudget,shiftWordBudget,bitTestBudget,prependCost,encodedListSpace_cons,encodedListSpace_nil]
    omega
  simpa only [Code.bitTestCode,Code.shiftedWord_testBit] using fit.mono cost

end Turing.PartrecToTM2.EvaluatorCodeFits
