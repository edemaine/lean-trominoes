/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecCellDecodeSpace
import LeanTrominoes.PartrecIntOffset
import LeanTrominoes.PartrecSubtractSpace

/-!
# Evaluator-space certificates for fixed offsets on encoded integers

The exact costs in this file follow the parity branches of the explicit
integer successor and predecessor programs.  Iterating those certificates
gives fitted calls for every compile-time integer offset, including on natural
machine inputs which do not need to be assumed to arise from `Encodable`.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def subtractTwoCost (number : Nat) : Nat :=
  predCost [number.pred] + predCost [number]

theorem subtractTwo (number : Nat) :
    EvaluatorCodeFits Code.subtractTwoCode [number]
      [number - 2] (subtractTwoCost number) := by
  have once := pred_named [number]
  have twice := pred_named [number.pred]
  have composed := comp twice once
  have output : number.pred.pred = number - 2 := by
    cases number with
    | zero => rfl
    | succ number =>
        cases number <;> rfl
  rw [← output]
  simpa [Code.subtractTwoCode, subtractTwoCost,
    Code.subtractStepList] using composed

def intSuccessorCost (number : Nat) : Nat :=
  if number.bodd then
    branchZeroSuccCost [number]
      [Code.intCodeSuccessor number] 1
      (intSignAtCost 0 [number])
      (subtractTwoCost number)
  else
    branchZeroZeroCost [number]
      [Code.intCodeSuccessor number] 0
      (intSignAtCost 0 [number])
      (addConstCost 2 [number])

theorem intSuccessor (number : Nat) :
    EvaluatorCodeFits Code.intSuccessorCode [number]
      [Code.intCodeSuccessor number]
      (intSuccessorCost number) := by
  cases parity : number.bodd with
  | false =>
      have selected := branchZero_zero
        (test := Code.intSignAtCode 0)
        (whenZero := Code.addConst 2)
        (whenSucc := Code.subtractTwoCode)
        (values := [number])
        (output := [Code.intCodeSuccessor number])
        (testValue := 0)
        (testCost := intSignAtCost 0 [number])
        (branchCost := addConstCost 2 [number])
        rfl
        (by simpa [parity] using intSignAt 0 [number])
        (by simpa [Code.intCodeSuccessor, parity] using
          addConst 2 [number])
      simpa [Code.intSuccessorCode, intSuccessorCost,
        parity] using selected
  | true =>
      have selected := branchZero_succ
        (test := Code.intSignAtCode 0)
        (whenZero := Code.addConst 2)
        (whenSucc := Code.subtractTwoCode)
        (values := [number])
        (output := [Code.intCodeSuccessor number])
        (testValue := 1)
        (testCost := intSignAtCost 0 [number])
        (branchCost := subtractTwoCost number)
        (by omega)
        (by simpa [parity] using intSignAt 0 [number])
        (by simpa [Code.intCodeSuccessor, parity] using
          subtractTwo number)
      simpa [Code.intSuccessorCode, intSuccessorCost,
        parity] using selected

def intPredecessorNonnegativeCost (number : Nat) : Nat :=
  if number = 0 then
    branchZeroZeroCost [number] [1] number
      (headCost [number]) (oneCost [number])
  else
    branchZeroSuccCost [number] [number - 2] number
      (headCost [number]) (subtractTwoCost number)

theorem intPredecessorNonnegative (number : Nat) :
    EvaluatorCodeFits Code.intPredecessorNonnegativeCode
      [number] [if number = 0 then 1 else number - 2]
      (intPredecessorNonnegativeCost number) := by
  by_cases zero : number = 0
  · subst number
    have selected := branchZero_zero
      (test := Code.head)
      (whenZero := Code.one)
      (whenSucc := Code.subtractTwoCode)
      (values := [0]) (output := [1])
      (testValue := 0) (testCost := headCost [0])
      (branchCost := oneCost [0]) rfl
      (by simpa using head [0])
      (by simpa using one [0])
    simpa [Code.intPredecessorNonnegativeCode,
      intPredecessorNonnegativeCost] using selected
  · have positive : 0 < number := Nat.pos_of_ne_zero zero
    have selected := branchZero_succ
      (test := Code.head)
      (whenZero := Code.one)
      (whenSucc := Code.subtractTwoCode)
      (values := [number]) (output := [number - 2])
      (testValue := number) (testCost := headCost [number])
      (branchCost := subtractTwoCost number) positive
      (by simpa using head [number])
      (subtractTwo number)
    simpa [Code.intPredecessorNonnegativeCode,
      intPredecessorNonnegativeCost, zero] using selected

def intPredecessorCost (number : Nat) : Nat :=
  if number.bodd then
    branchZeroSuccCost [number]
      [Code.intCodePredecessor number] 1
      (intSignAtCost 0 [number])
      (addConstCost 2 [number])
  else
    branchZeroZeroCost [number]
      [Code.intCodePredecessor number] 0
      (intSignAtCost 0 [number])
      (intPredecessorNonnegativeCost number)

theorem intPredecessor (number : Nat) :
    EvaluatorCodeFits Code.intPredecessorCode [number]
      [Code.intCodePredecessor number]
      (intPredecessorCost number) := by
  cases parity : number.bodd with
  | false =>
      have selected := branchZero_zero
        (test := Code.intSignAtCode 0)
        (whenZero := Code.intPredecessorNonnegativeCode)
        (whenSucc := Code.addConst 2)
        (values := [number])
        (output := [Code.intCodePredecessor number])
        (testValue := 0)
        (testCost := intSignAtCost 0 [number])
        (branchCost := intPredecessorNonnegativeCost number)
        rfl
        (by simpa [parity] using intSignAt 0 [number])
        (by simpa [Code.intCodePredecessor, parity] using
          intPredecessorNonnegative number)
      simpa [Code.intPredecessorCode, intPredecessorCost,
        parity] using selected
  | true =>
      have selected := branchZero_succ
        (test := Code.intSignAtCode 0)
        (whenZero := Code.intPredecessorNonnegativeCode)
        (whenSucc := Code.addConst 2)
        (values := [number])
        (output := [Code.intCodePredecessor number])
        (testValue := 1)
        (testCost := intSignAtCost 0 [number])
        (branchCost := addConstCost 2 [number])
        (by omega)
        (by simpa [parity] using intSignAt 0 [number])
        (by simpa [Code.intCodePredecessor, parity] using
          addConst 2 [number])
      simpa [Code.intPredecessorCode, intPredecessorCost,
        parity] using selected

def intCodeAddNat : Nat → Nat → Nat
  | 0, number => number
  | amount + 1, number =>
      Code.intCodeSuccessor (intCodeAddNat amount number)

def intAddNatCost : Nat → Nat → Nat
  | 0, number => headCost [number]
  | amount + 1, number =>
      intSuccessorCost (intCodeAddNat amount number) +
        intAddNatCost amount number

theorem intAddNat (amount number : Nat) :
    EvaluatorCodeFits (Code.intAddNatCode amount) [number]
      [intCodeAddNat amount number]
      (intAddNatCost amount number) := by
  induction amount with
  | zero =>
      simpa [Code.intAddNatCode, intCodeAddNat,
        intAddNatCost] using head [number]
  | succ amount induction =>
      simpa [Code.intAddNatCode, intCodeAddNat,
        intAddNatCost] using
        comp (intSuccessor (intCodeAddNat amount number))
          induction

def intCodeSubtractNat : Nat → Nat → Nat
  | 0, number => number
  | amount + 1, number =>
      Code.intCodePredecessor (intCodeSubtractNat amount number)

def intSubtractNatCost : Nat → Nat → Nat
  | 0, number => headCost [number]
  | amount + 1, number =>
      intPredecessorCost (intCodeSubtractNat amount number) +
        intSubtractNatCost amount number

theorem intSubtractNat (amount number : Nat) :
    EvaluatorCodeFits (Code.intSubtractNatCode amount) [number]
      [intCodeSubtractNat amount number]
      (intSubtractNatCost amount number) := by
  induction amount with
  | zero =>
      simpa [Code.intSubtractNatCode, intCodeSubtractNat,
        intSubtractNatCost] using head [number]
  | succ amount induction =>
      simpa [Code.intSubtractNatCode, intCodeSubtractNat,
        intSubtractNatCost] using
        comp (intPredecessor (intCodeSubtractNat amount number))
          induction

def intOffsetResultCode (offset : Int) (number : Nat) : Nat :=
  match offset with
  | .ofNat amount => intCodeAddNat amount number
  | .negSucc amount => intCodeSubtractNat (amount + 1) number

def intOffsetCost (offset : Int) (number : Nat) : Nat :=
  match offset with
  | .ofNat amount => intAddNatCost amount number
  | .negSucc amount => intSubtractNatCost (amount + 1) number

theorem intOffset (offset : Int) (number : Nat) :
    EvaluatorCodeFits (Code.intOffsetCode offset) [number]
      [intOffsetResultCode offset number]
      (intOffsetCost offset number) := by
  cases offset with
  | ofNat amount =>
      simpa [Code.intOffsetCode, intOffsetResultCode,
        intOffsetCost] using intAddNat amount number
  | negSucc amount =>
      simpa [Code.intOffsetCode, intOffsetResultCode,
        intOffsetCost] using intSubtractNat (amount + 1) number

theorem intCodeAddNat_encode (amount : Nat) (value : Int) :
    intCodeAddNat amount (Encodable.encode value) =
      Encodable.encode (value + amount) := by
  induction amount with
  | zero => simp [intCodeAddNat]
  | succ amount induction =>
      rw [intCodeAddNat, induction, Code.intCodeSuccessor_encode]
      congr 1
      push_cast
      ring

theorem intCodeSubtractNat_encode (amount : Nat) (value : Int) :
    intCodeSubtractNat amount (Encodable.encode value) =
      Encodable.encode (value - amount) := by
  induction amount with
  | zero => simp [intCodeSubtractNat]
  | succ amount induction =>
      rw [intCodeSubtractNat, induction,
        Code.intCodePredecessor_encode]
      congr 1
      push_cast
      ring

@[simp]
theorem intOffsetResultCode_encode (offset value : Int) :
    intOffsetResultCode offset (Encodable.encode value) =
      Encodable.encode (value + offset) := by
  cases offset with
  | ofNat amount =>
      simpa [intOffsetResultCode] using
        intCodeAddNat_encode amount value
  | negSucc amount =>
      rw [intOffsetResultCode,
        intCodeSubtractNat_encode]
      congr 1

def intOffsetUnit (amount number : Nat) : Nat :=
  encodedListSpace [2 * (number + 2 * amount) + 8] + 1

/-- The fixed-offset workspace unit is linear in the bit lengths of the
encoded integer and the offset magnitude. -/
theorem intOffsetUnit_le_linear (amount number : Nat) :
    intOffsetUnit amount number ≤
      20 * ((Computability.encodeNat number).length +
        (Computability.encodeNat amount).length + 1) := by
  have doubledAmount := encodeNat_mul_length_le_sum 2 amount
  have inner := encodeNat_add_length_le_sum number (2 * amount)
  have doubled := encodeNat_mul_length_le_sum 2 (number + 2 * amount)
  have final := encodeNat_add_length_le_sum
    (2 * (number + 2 * amount)) 8
  have twoBits :
      (Computability.encodeNat 2).length = 2 := by native_decide
  have eightBits :
      (Computability.encodeNat 8).length = 4 := by native_decide
  simp only [intOffsetUnit,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

private theorem intPrimitiveCost_le_unit
    (number limit : Nat) (bounded : 2 * number + 8 ≤ limit) :
    intSuccessorCost number ≤
        10000000000 * (encodedListSpace [limit] + 1) ∧
      intPredecessorCost number ≤
        10000000000 * (encodedListSpace [limit] + 1) := by
  have numberBound : number ≤ limit := by omega
  have successorBound : number + 1 ≤ limit := by omega
  have plusTwoBound : number + 2 ≤ limit := by omega
  have plusThreeBound : number + 3 ≤ limit := by omega
  have predBound : number.pred ≤ limit :=
    (Nat.pred_le number).trans numberBound
  have predPredBound : number.pred.pred ≤ limit :=
    (Nat.pred_le number.pred).trans predBound
  have predSuccBound : number.pred + 1 ≤ limit :=
    (Nat.add_le_add_right (Nat.pred_le number) 1).trans
      successorBound
  have minusTwoBound : number - 2 ≤ limit := by omega
  have quotientLe : number.div2 ≤ number := by
    have identity := Nat.bodd_add_div2 number
    omega
  have quotientBound : number.div2 ≤ limit :=
    quotientLe.trans numberBound
  have parityBound : number.bodd.toNat ≤ limit := by
    have small : number.bodd.toNat ≤ 1 := by
      cases number.bodd <;> decide
    omega
  have numberBits := encodeNat_length_mono numberBound
  have successorBits := encodeNat_length_mono successorBound
  have plusTwoBits := encodeNat_length_mono plusTwoBound
  have plusThreeBits := encodeNat_length_mono plusThreeBound
  have predBits := encodeNat_length_mono predBound
  have predPredBits := encodeNat_length_mono predPredBound
  have predSuccBits := encodeNat_length_mono predSuccBound
  have minusTwoBits := encodeNat_length_mono minusTwoBound
  have quotientBits := encodeNat_length_mono quotientBound
  have parityBits := encodeNat_length_mono parityBound
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have predLocal := predCost_singleton_le_linear number
  have predLimit : 2 * number + 4 ≤ limit := by omega
  have predLimitBits := encodeNat_length_mono predLimit
  have predCostBound :
      predCost [number] ≤
        1000000 * (encodedListSpace [limit] + 1) :=
    predLocal.trans (Nat.mul_le_mul_left _ (by
      simpa [encodedListSpace_cons,
        encodedListSpace_nil] using predLimitBits))
  have predPredLocal :=
    predCost_singleton_le_linear number.pred
  have predPredLimit : 2 * number.pred + 4 ≤ limit := by
    calc
      2 * number.pred + 4 ≤ 2 * number + 4 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left 2 (Nat.pred_le number)) 4
      _ ≤ limit := by omega
  have predPredLimitBits := encodeNat_length_mono predPredLimit
  have predPredCostBound :
      predCost [number.pred] ≤
        1000000 * (encodedListSpace [limit] + 1) :=
    predPredLocal.trans (Nat.mul_le_mul_left _ (by
      simpa [encodedListSpace_cons,
        encodedListSpace_nil] using predPredLimitBits))
  have subtractTwoBound :
      subtractTwoCost number ≤
        2000000 * (encodedListSpace [limit] + 1) := by
    simp only [subtractTwoCost]
    omega
  cases number with
  | zero =>
      simp [intSuccessorCost, intPredecessorCost,
        intPredecessorNonnegativeCost,
        Code.intCodeSuccessor, Code.intCodePredecessor,
        branchZeroZeroCost,
        branchZeroTestCost, prependCost,
        intSignAtCost, intViewAtCost, div2ParityCost,
        binaryDiv2Cost, addConstCost,
        getCost, dropCost, headCost, idCost, nilCost,
        oneCost, zeroCost, zeroPrimeCost, tailCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits, twoBits] at *
      omega
  | succ number =>
      have rearrangedPlusTwoBits :=
        encodeNat_length_mono
          (show number + 2 + 1 ≤ limit by omega)
      cases parity : number.bodd <;>
        simp [intSuccessorCost, intPredecessorCost,
          intPredecessorNonnegativeCost,
          Code.intCodeSuccessor, Code.intCodePredecessor,
          branchZeroZeroCost, branchZeroSuccCost,
          branchZeroTestCost, prependCost,
          intSignAtCost, intViewAtCost, div2ParityCost,
          binaryDiv2Cost, addConstCost,
          getCost, dropCost, headCost, idCost, nilCost,
          zeroPrimeCost, tailCost, succCost,
          encodedListSpace_cons, encodedListSpace_nil,
          parity, zeroBits, oneBits, twoBits] at * <;>
        omega

theorem intSuccessorCost_le_linear (number : Nat) :
    intSuccessorCost number ≤
      10000000000 * intOffsetUnit 0 number := by
  simpa [intOffsetUnit] using
    (intPrimitiveCost_le_unit number (2 * number + 8)
      (by omega)).1

theorem intPredecessorCost_le_linear (number : Nat) :
    intPredecessorCost number ≤
      10000000000 * intOffsetUnit 0 number := by
  simpa [intOffsetUnit] using
    (intPrimitiveCost_le_unit number (2 * number + 8)
      (by omega)).2

private theorem intCodeSuccessor_le (number : Nat) :
    Code.intCodeSuccessor number ≤ number + 2 := by
  simp only [Code.intCodeSuccessor]
  split <;> omega

private theorem intCodePredecessor_le (number : Nat) :
    Code.intCodePredecessor number ≤ number + 2 := by
  simp only [Code.intCodePredecessor]
  split
  · omega
  · split <;> omega

theorem intCodeAddNat_le (amount number : Nat) :
    intCodeAddNat amount number ≤ number + 2 * amount := by
  induction amount with
  | zero => simp [intCodeAddNat]
  | succ amount induction =>
      rw [intCodeAddNat]
      exact (intCodeSuccessor_le _).trans (by omega)

theorem intCodeSubtractNat_le (amount number : Nat) :
    intCodeSubtractNat amount number ≤ number + 2 * amount := by
  induction amount with
  | zero => simp [intCodeSubtractNat]
  | succ amount induction =>
      rw [intCodeSubtractNat]
      exact (intCodePredecessor_le _).trans (by omega)

private theorem headCost_le_offsetUnit (amount number : Nat) :
    headCost [number] ≤
      10000000000 * intOffsetUnit amount number := by
  have numberBound :
      number ≤ 2 * (number + 2 * amount) + 8 := by omega
  have successorBound :
      number + 1 ≤ 2 * (number + 2 * amount) + 8 := by omega
  have numberBits := encodeNat_length_mono numberBound
  have successorBits := encodeNat_length_mono successorBound
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [intOffsetUnit, headCost, idCost, nilCost,
    tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits] at *
  omega

private theorem intOffsetUnit_mono_amount
    (amount number : Nat) :
    intOffsetUnit amount number ≤
      intOffsetUnit (amount + 1) number := by
  have limitBound :
      2 * (number + 2 * amount) + 8 ≤
        2 * (number + 2 * (amount + 1)) + 8 := by omega
  have bits := encodeNat_length_mono limitBound
  simpa [intOffsetUnit, encodedListSpace_cons,
    encodedListSpace_nil] using Nat.add_le_add_right bits 2

theorem intAddNatCost_le_linear (amount number : Nat) :
    intAddNatCost amount number ≤
      10000000000 * (amount + 1) *
        intOffsetUnit amount number := by
  induction amount with
  | zero =>
      simpa [intAddNatCost] using
        headCost_le_offsetUnit 0 number
  | succ amount induction =>
      let value := intCodeAddNat amount number
      let limit := 2 * (number + 2 * (amount + 1)) + 8
      have valueBound : value ≤ number + 2 * amount := by
        exact intCodeAddNat_le amount number
      have primitiveBound : 2 * value + 8 ≤ limit := by
        simp only [limit]
        omega
      have stepBound :
          intSuccessorCost value ≤
            10000000000 * intOffsetUnit (amount + 1) number := by
        have primitiveLocal :=
          (intPrimitiveCost_le_unit value limit primitiveBound).1
        simpa [intOffsetUnit, limit] using primitiveLocal
      have unitBound := intOffsetUnit_mono_amount amount number
      have previousBound :
          intAddNatCost amount number ≤
            10000000000 * (amount + 1) *
              intOffsetUnit (amount + 1) number :=
        induction.trans
          (Nat.mul_le_mul_left
            (10000000000 * (amount + 1)) unitBound)
      rw [intAddNatCost]
      change
        intSuccessorCost value + intAddNatCost amount number ≤ _
      calc
        _ ≤ 10000000000 * intOffsetUnit (amount + 1) number +
              10000000000 * (amount + 1) *
                intOffsetUnit (amount + 1) number :=
          Nat.add_le_add stepBound previousBound
        _ = 10000000000 * (amount + 1 + 1) *
              intOffsetUnit (amount + 1) number := by ring

theorem intSubtractNatCost_le_linear (amount number : Nat) :
    intSubtractNatCost amount number ≤
      10000000000 * (amount + 1) *
        intOffsetUnit amount number := by
  induction amount with
  | zero =>
      simpa [intSubtractNatCost] using
        headCost_le_offsetUnit 0 number
  | succ amount induction =>
      let value := intCodeSubtractNat amount number
      let limit := 2 * (number + 2 * (amount + 1)) + 8
      have valueBound : value ≤ number + 2 * amount := by
        exact intCodeSubtractNat_le amount number
      have primitiveBound : 2 * value + 8 ≤ limit := by
        simp only [limit]
        omega
      have stepBound :
          intPredecessorCost value ≤
            10000000000 * intOffsetUnit (amount + 1) number := by
        have primitiveLocal :=
          (intPrimitiveCost_le_unit value limit primitiveBound).2
        simpa [intOffsetUnit, limit] using primitiveLocal
      have unitBound := intOffsetUnit_mono_amount amount number
      have previousBound :
          intSubtractNatCost amount number ≤
            10000000000 * (amount + 1) *
              intOffsetUnit (amount + 1) number :=
        induction.trans
          (Nat.mul_le_mul_left
            (10000000000 * (amount + 1)) unitBound)
      rw [intSubtractNatCost]
      change
        intPredecessorCost value +
            intSubtractNatCost amount number ≤ _
      calc
        _ ≤ 10000000000 * intOffsetUnit (amount + 1) number +
              10000000000 * (amount + 1) *
                intOffsetUnit (amount + 1) number :=
          Nat.add_le_add stepBound previousBound
        _ = 10000000000 * (amount + 1 + 1) *
              intOffsetUnit (amount + 1) number := by ring

def intOffsetAmount : Int → Nat
  | .ofNat amount => amount
  | .negSucc amount => amount + 1

theorem intOffsetResultCode_le (offset : Int) (number : Nat) :
    intOffsetResultCode offset number ≤
      number + 2 * intOffsetAmount offset := by
  cases offset with
  | ofNat amount =>
      simpa [intOffsetResultCode, intOffsetAmount] using
        intCodeAddNat_le amount number
  | negSucc amount =>
      simpa [intOffsetResultCode, intOffsetAmount] using
        intCodeSubtractNat_le (amount + 1) number

/-- Applying a fixed integer offset increases encoded length by at most a
constant-factor expression in the input and offset-magnitude lengths. -/
theorem intOffsetResultCode_length_le (offset : Int) (number : Nat) :
    (Computability.encodeNat
      (intOffsetResultCode offset number)).length ≤
      10 * ((Computability.encodeNat number).length +
        (Computability.encodeNat (intOffsetAmount offset)).length + 1) := by
  have result := encodeNat_length_mono
    (intOffsetResultCode_le offset number)
  have doubled := encodeNat_mul_length_le_sum 2
    (intOffsetAmount offset)
  have summed := encodeNat_add_length_le_sum number
    (2 * intOffsetAmount offset)
  have twoBits :
      (Computability.encodeNat 2).length = 2 := by native_decide
  omega

/-- Every fixed encoded-integer offset uses space linear in one encoded
envelope.  The coefficient depends only linearly on the compile-time offset.-/
theorem intOffsetCost_le_linear (offset : Int) (number : Nat) :
    intOffsetCost offset number ≤
      10000000000 * (intOffsetAmount offset + 1) *
        intOffsetUnit (intOffsetAmount offset) number := by
  cases offset with
  | ofNat amount =>
      simpa [intOffsetCost, intOffsetAmount] using
        intAddNatCost_le_linear amount number
  | negSucc amount =>
      simpa [intOffsetCost, intOffsetAmount] using
        intSubtractNatCost_le_linear (amount + 1) number

end EvaluatorCodeFits

end PartrecToTM2
end Turing
