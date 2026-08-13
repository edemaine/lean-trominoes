/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecCellDecode
import LeanTrominoes.PartrecListCode

/-!
# Explicit fixed offsets on encoded integers

Mathlib encodes nonnegative integers as even naturals and negative integers as
odd naturals.  Successor and predecessor therefore need only a parity branch
and a fixed addition or truncated subtraction by two.  Finite composition
then implements addition by any compile-time integer constant.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- Subtract two from the input head, truncating at zero. -/
def subtractTwoCode : Code := pred.comp pred

@[simp]
theorem subtractTwoCode_eval (number : Nat) :
    subtractTwoCode.eval [number] = pure [number - 2] := by
  simp [subtractTwoCode]
  omega

/-- Arithmetic successor on a natural encoding of an integer. -/
def intCodeSuccessor (number : Nat) : Nat :=
  if number.bodd then number - 2 else number + 2

/-- Arithmetic predecessor on a natural encoding of an integer. -/
def intCodePredecessor (number : Nat) : Nat :=
  if number.bodd then number + 2
  else if number = 0 then 1 else number - 2

theorem intCodeSuccessor_encode (value : Int) :
    intCodeSuccessor (Encodable.encode value) =
      Encodable.encode (value + 1) := by
  cases value with
  | ofNat value =>
      change intCodeSuccessor (2 * value) = 2 * (value + 1)
      simp [intCodeSuccessor]
      omega
  | negSucc value =>
      cases value with
      | zero =>
          change intCodeSuccessor 1 = 0
          decide
      | succ value =>
          change
            intCodeSuccessor (2 * (value + 1) + 1) =
              2 * value + 1
          simp [intCodeSuccessor]
          omega

theorem intCodePredecessor_encode (value : Int) :
    intCodePredecessor (Encodable.encode value) =
      Encodable.encode (value - 1) := by
  cases value with
  | ofNat value =>
      cases value with
      | zero =>
          change intCodePredecessor 0 = 1
          decide
      | succ value =>
          have difference :
              (Int.ofNat (value + 1)) - 1 = Int.ofNat value := by
            simp
          rw [difference]
          change
            intCodePredecessor (2 * (value + 1)) = 2 * value
          simp [intCodePredecessor]
          omega
  | negSucc value =>
      change
        intCodePredecessor (2 * value + 1) =
          2 * (value + 1) + 1
      simp [intCodePredecessor]
      omega

/-- Add one to the integer represented by the input head. -/
def intSuccessorCode : Code :=
  branchZero (intSignAtCode 0)
    (addConst 2) subtractTwoCode

theorem intSuccessorCode_eval_nat (number : Nat) :
    intSuccessorCode.eval [number] =
      pure [intCodeSuccessor number] := by
  cases parity : number.bodd with
  | false =>
      have evaluated := branchZero_eval_zero_at
        (intSignAtCode 0) (addConst 2) subtractTwoCode
        [number] 0 (by simp [parity]) [number + 2]
        (by simp) rfl
      simpa [intSuccessorCode, intCodeSuccessor, parity] using evaluated
  | true =>
      have evaluated := branchZero_eval_succ_at
        (intSignAtCode 0) (addConst 2) subtractTwoCode
        [number] 1 (by simp [parity]) [number - 2]
        (subtractTwoCode_eval number) (by omega)
      simpa [intSuccessorCode, intCodeSuccessor, parity] using evaluated

@[simp]
theorem intSuccessorCode_eval (value : Int) :
    intSuccessorCode.eval [Encodable.encode value] =
      pure [Encodable.encode (value + 1)] := by
  rw [intSuccessorCode_eval_nat, intCodeSuccessor_encode]

/-- Subtract one from the integer represented by the input head. -/
def intPredecessorNonnegativeCode : Code :=
  branchZero head one subtractTwoCode

theorem intPredecessorNonnegativeCode_eval_nat (number : Nat) :
    intPredecessorNonnegativeCode.eval [number] =
      pure [if number = 0 then 1 else number - 2] := by
  by_cases zero : number = 0
  · subst number
    exact branchZero_eval_zero_at head one subtractTwoCode
      [0] 0 (by simp) [1] (by simp) rfl
  · have evaluated := branchZero_eval_succ_at
      head one subtractTwoCode [number] number
      (by simp) [number - 2]
      (subtractTwoCode_eval number) (Nat.pos_of_ne_zero zero)
    simpa [intPredecessorNonnegativeCode, zero] using evaluated

@[simp]
theorem intPredecessorNonnegativeCode_eval (value : Nat) :
    intPredecessorNonnegativeCode.eval
        [Encodable.encode (Int.ofNat value)] =
      pure [Encodable.encode ((Int.ofNat value) - 1)] := by
  rw [intPredecessorNonnegativeCode_eval_nat]
  cases value with
  | zero => rfl
  | succ value =>
      have difference :
          (Int.ofNat (value + 1)) - 1 = Int.ofNat value := by
        simp
      rw [difference]
      change
        pure [if 2 * (value + 1) = 0 then 1
          else 2 * (value + 1) - 2] = pure [2 * value]
      simp
      omega

/-- Subtract one from an encoded integer. -/
def intPredecessorCode : Code :=
  branchZero (intSignAtCode 0)
    intPredecessorNonnegativeCode (addConst 2)

theorem intPredecessorCode_eval_nat (number : Nat) :
    intPredecessorCode.eval [number] =
      pure [intCodePredecessor number] := by
  cases parity : number.bodd with
  | false =>
      have evaluated := branchZero_eval_zero_at
        (intSignAtCode 0) intPredecessorNonnegativeCode
        (addConst 2) [number] 0 (by simp [parity])
        [if number = 0 then 1 else number - 2]
        (intPredecessorNonnegativeCode_eval_nat number) rfl
      simpa [intPredecessorCode, intCodePredecessor,
        parity] using evaluated
  | true =>
      have evaluated := branchZero_eval_succ_at
        (intSignAtCode 0) intPredecessorNonnegativeCode
        (addConst 2) [number] 1 (by simp [parity])
        [number + 2] (by simp) (by omega)
      simpa [intPredecessorCode, intCodePredecessor,
        parity] using evaluated

@[simp]
theorem intPredecessorCode_eval (value : Int) :
    intPredecessorCode.eval [Encodable.encode value] =
      pure [Encodable.encode (value - 1)] := by
  rw [intPredecessorCode_eval_nat, intCodePredecessor_encode]

/-- Add a natural constant to an encoded integer. -/
def intAddNatCode : Nat → Code
  | 0 => head
  | amount + 1 => intSuccessorCode.comp (intAddNatCode amount)

@[simp]
theorem intAddNatCode_eval (amount : Nat) (value : Int) :
    (intAddNatCode amount).eval [Encodable.encode value] =
      pure [Encodable.encode (value + amount)] := by
  induction amount with
  | zero => simp [intAddNatCode]
  | succ amount induction =>
      calc
        _ = intSuccessorCode.eval
            [Encodable.encode (value + amount)] := by
          simp [intAddNatCode, induction]
        _ = pure [Encodable.encode ((value + amount) + 1)] :=
          intSuccessorCode_eval _
        _ = pure [Encodable.encode (value + (amount + 1))] := by
          congr 3
          ring

/-- Subtract a natural constant from an encoded integer. -/
def intSubtractNatCode : Nat → Code
  | 0 => head
  | amount + 1 => intPredecessorCode.comp (intSubtractNatCode amount)

@[simp]
theorem intSubtractNatCode_eval (amount : Nat) (value : Int) :
    (intSubtractNatCode amount).eval [Encodable.encode value] =
      pure [Encodable.encode (value - amount)] := by
  induction amount with
  | zero => simp [intSubtractNatCode]
  | succ amount induction =>
      calc
        _ = intPredecessorCode.eval
            [Encodable.encode (value - amount)] := by
          simp [intSubtractNatCode, induction]
        _ = pure [Encodable.encode ((value - amount) - 1)] :=
          intPredecessorCode_eval _
        _ = pure [Encodable.encode (value - (amount + 1))] := by
          congr 3
          ring

/-- Add a fixed integer offset to an encoded integer. -/
def intOffsetCode : Int → Code
  | .ofNat amount => intAddNatCode amount
  | .negSucc amount => intSubtractNatCode (amount + 1)

@[simp]
theorem intOffsetCode_eval (offset value : Int) :
    (intOffsetCode offset).eval [Encodable.encode value] =
      pure [Encodable.encode (value + offset)] := by
  cases offset with
  | ofNat amount =>
      rw [intOffsetCode]
      exact intAddNatCode_eval amount value
  | negSucc amount =>
      rw [intOffsetCode, intSubtractNatCode_eval]
      congr 3

end Turing.ToPartrec.Code
