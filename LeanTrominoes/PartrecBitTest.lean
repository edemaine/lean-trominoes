/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBinaryLength
import LeanTrominoes.PartrecDivision

/-! # Bit lookup by repeated halving, without constructing a power of two -/

namespace Turing.ToPartrec.Code

def shiftedWord (word index : Nat) : Nat := (Nat.div2^[index]) word

theorem shiftedWord_le (word index : Nat) : shiftedWord word index ≤ word := by
  induction index generalizing word with
  | zero => rfl
  | succ index ih =>
    rw [shiftedWord,Function.iterate_succ_apply]
    exact (ih word.div2).trans (by simp [Nat.div2_val]; omega)

theorem shiftedWord_testBit (word index : Nat) :
    (shiftedWord word index).testBit 0 = word.testBit index := by
  induction index generalizing word with
  | zero => rfl
  | succ index ih =>
    rw [shiftedWord,Function.iterate_succ_apply]
    exact (ih word.div2).trans (by simp [Nat.testBit_succ,Nat.div2_val])

theorem shiftWord_eval (word index : Nat) :
    (flatIterate binaryDiv2Code).eval [index,word] = pure [shiftedWord word index] := by
  rw [flatIterate,fix_eval]
  apply Part.eq_some_iff.mpr
  induction index generalizing word with
  | zero =>
    apply PFun.mem_fix_iff.mpr
    left
    simp [flatCountdownBody_zero_eval,shiftedWord]
  | succ index ih =>
    apply PFun.mem_fix_iff.mpr
    right
    refine ⟨[index,word.div2],?_,?_⟩
    · simp [flatCountdownBody]
    · simpa [shiftedWord,Function.iterate_succ_apply] using ih word.div2

def parityCode : Code := (get 1).comp (divisionCode.comp (prepend head (numeral 2)))

theorem parityCode_eval (word : Nat) : parityCode.eval [word] = pure [(word.testBit 0).toNat] := by
  have h : word % 2 = 0 ∨ word % 2 = 1 := by omega
  rcases h with h | h <;> simp [parityCode,Part.bind_eq_bind,Nat.testBit_zero,h]

/-- Input `[word,index]`; output the selected bit as zero or one. -/
def bitTestCode : Code := parityCode.comp ((flatIterate binaryDiv2Code).comp (prepend (get 1) (get 0)))

theorem bitTestCode_eval (word index : Nat) : bitTestCode.eval [word,index] = pure [(word.testBit index).toNat] := by
  have bit := shiftedWord_testBit word index
  simp only [Nat.testBit_zero] at bit
  simp [bitTestCode,shiftWord_eval,parityCode_eval,Part.bind_eq_bind,bit]

end Turing.ToPartrec.Code
