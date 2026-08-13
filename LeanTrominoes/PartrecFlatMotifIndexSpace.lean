/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecDynamicDropSpace
import LeanTrominoes.PartrecFlatMotifIndex
import LeanTrominoes.PartrecMultiplySpace

/-!
# Evaluator-space certificate for dynamic flat motif indexing

The native motif indexer computes `headerLength + 2 * index`, dynamically
drops that prefix, and projects one of the next two coordinate fields.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def flatMotifIndexProductArgumentsCost
    (indexField : Nat) (values : List Nat) : Nat :=
  prependCost values [2] [values[indexField]?.getD 0]
    (numeralCost 2 values) (getCost indexField values)

theorem flatMotifIndexProductArguments
    (indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.flatMotifIndexProductArgumentsCode indexField)
      values [2, values[indexField]?.getD 0]
      (flatMotifIndexProductArgumentsCost indexField values) := by
  simpa [Code.flatMotifIndexProductArgumentsCode,
    flatMotifIndexProductArgumentsCost, prependCost] using
    prepend (numeral 2 values) (get indexField values)

def flatMotifIndexProductCost
    (indexField : Nat) (values : List Nat) : Nat :=
  natMultiplyCost 2 (values[indexField]?.getD 0) +
    flatMotifIndexProductArgumentsCost indexField values

theorem flatMotifIndexProduct
    (indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.flatMotifIndexProductCode indexField) values
      [2 * values[indexField]?.getD 0]
      (flatMotifIndexProductCost indexField values) := by
  simpa [Code.flatMotifIndexProductCode, flatMotifIndexProductCost] using
    comp (natMultiply 2 (values[indexField]?.getD 0))
      (flatMotifIndexProductArguments indexField values)

def flatMotifIndexOffsetCost
    (headerLength indexField : Nat) (values : List Nat) : Nat :=
  addConstCost headerLength [2 * values[indexField]?.getD 0] +
    flatMotifIndexProductCost indexField values

theorem flatMotifIndexOffset
    (headerLength indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.flatMotifIndexOffsetCode headerLength indexField) values
      [headerLength + 2 * values[indexField]?.getD 0]
      (flatMotifIndexOffsetCost headerLength indexField values) := by
  simpa [Code.flatMotifIndexOffsetCode, flatMotifIndexOffsetCost,
    Nat.add_comm] using
    comp (addConst headerLength [2 * values[indexField]?.getD 0])
      (flatMotifIndexProduct indexField values)

def flatMotifIndexDropInputCost
    (headerLength indexField : Nat) (values : List Nat) : Nat :=
  let offset := headerLength + 2 * values[indexField]?.getD 0
  prependCost values [offset] values
    (flatMotifIndexOffsetCost headerLength indexField values) (idCost values)

theorem flatMotifIndexDropInput
    (headerLength indexField : Nat) (values : List Nat) :
    let offset := headerLength + 2 * values[indexField]?.getD 0
    EvaluatorCodeFits
      (Code.flatMotifIndexDropInputCode headerLength indexField) values
      (offset :: values)
      (flatMotifIndexDropInputCost headerLength indexField values) := by
  simp only
  simpa [Code.flatMotifIndexDropInputCode,
    flatMotifIndexDropInputCost, prependCost] using
    prepend (flatMotifIndexOffset headerLength indexField values) (id values)

def flatMotifIndexedSuffixCost
    (headerLength indexField : Nat) (values : List Nat) : Nat :=
  let offset := headerLength + 2 * values[indexField]?.getD 0
  dynamicDropCost offset values +
    flatMotifIndexDropInputCost headerLength indexField values

theorem flatMotifIndexedSuffix
    (headerLength indexField : Nat) (values : List Nat) :
    let offset := headerLength + 2 * values[indexField]?.getD 0
    EvaluatorCodeFits
      (Code.flatMotifIndexedSuffixCode headerLength indexField) values
      (values.drop offset)
      (flatMotifIndexedSuffixCost headerLength indexField values) := by
  simp only
  let offset := headerLength + 2 * values[indexField]?.getD 0
  simpa [Code.flatMotifIndexedSuffixCode, flatMotifIndexedSuffixCost,
    offset] using
    comp (dynamicDrop offset values)
      (flatMotifIndexDropInput headerLength indexField values)

def flatMotifCellFieldAtCost
    (headerLength indexField outputField : Nat)
    (values : List Nat) : Nat :=
  let offset := headerLength + 2 * values[indexField]?.getD 0
  getCost outputField (values.drop offset) +
    flatMotifIndexedSuffixCost headerLength indexField values

theorem flatMotifCellFieldAt
    (headerLength indexField outputField : Nat) (values : List Nat) :
    let offset := headerLength + 2 * values[indexField]?.getD 0
    EvaluatorCodeFits
      (Code.flatMotifCellFieldAtCode headerLength indexField outputField)
      values [(values.drop offset)[outputField]?.getD 0]
      (flatMotifCellFieldAtCost headerLength indexField outputField values) := by
  simp only
  let offset := headerLength + 2 * values[indexField]?.getD 0
  simpa [Code.flatMotifCellFieldAtCode, flatMotifCellFieldAtCost, offset] using
    comp (get outputField (values.drop offset))
      (flatMotifIndexedSuffix headerLength indexField values)

/-! ## Fixed transition-index bounds -/

def flatMotifIndexUnit (values : List Nat) : Nat :=
  encodedListSpace values + 10

def flatMotifIndexSpaceBound (values : List Nat) : Nat :=
  1000000000000000000000000000000000000000000000000 *
    (flatMotifIndexUnit values) ^ 2

theorem flatMotifIndexSelectedSpace_le
    (index : Nat) (values : List Nat) :
    encodedListSpace [values[index]?.getD 0] ≤
      encodedListSpace values + 1 := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [List.getElem?_cons_zero, Option.getD_some] at *
          exact listCodeEncodedListSpace_singleton_headI_le
            (value :: values)
  | succ index induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          have tail := induction values
          simp only [List.getElem?_cons_succ] at tail ⊢
          exact tail.trans (Nat.add_le_add_right
            (listCodeEncodedListSpace_tail_le (value :: values)) 1)

def flatMotifIndexLinearBound (values : List Nat) : Nat :=
  1000000000000000000000000000000000000000000000 *
    (flatMotifIndexUnit values + 1)

set_option maxHeartbeats 800000 in
theorem flatMotifIndexMultiplyCost_le_unit (values : List Nat) :
    natMultiplyCost 2 (values[1]?.getD 0) ≤
      100000000000000000000000000000000000000 *
        flatMotifIndexUnit values := by
  let index := values[1]?.getD 0
  let unit := flatMotifIndexUnit values
  let limit := 16 * (2 + index + 2 * index + 10) + 100
  have selectedSpace := flatMotifIndexSelectedSpace_le 1 values
  have selectedSpace' : encodedListSpace [index] ≤
      encodedListSpace values + 1 := by
    simpa [index] using selectedSpace
  have selectedBits' : (Computability.encodeNat index).length + 1 ≤
      encodedListSpace values + 1 := by
    simpa [encodedListSpace_cons] using selectedSpace'
  have selectedUnit : encodedListSpace [index] ≤ unit := by
    dsimp [unit, flatMotifIndexUnit]
    omega
  have indexBits : (Computability.encodeNat index).length + 1 ≤ unit := by
    simpa [encodedListSpace_cons] using selectedUnit
  have doubleBits := encodeNat_mul_length_le_sum 2 index
  have sum1 := encodeNat_add_length_le_sum 2 index
  have sum2 := encodeNat_add_length_le_sum (2 + index) (2 * index)
  have sum3 := encodeNat_add_length_le_sum (2 + index + 2 * index) 10
  have scaled := encodeNat_mul_length_le_sum 16
    (2 + index + 2 * index + 10)
  have final := encodeNat_add_length_le_sum
    (16 * (2 + index + 2 * index + 10)) 100
  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
  have tenBits : (Computability.encodeNat 10).length = 4 := by native_decide
  have sixteenBits : (Computability.encodeNat 16).length = 5 := by
    native_decide
  have hundredBits : (Computability.encodeNat 100).length = 7 := by
    native_decide
  have limitBits :
      (Computability.encodeNat limit).length + 2 ≤ 100 * unit := by
    simp only [limit] at final ⊢
    omega
  have raw := natMultiplyCost_le_linear 2 index
  change natMultiplyCost 2 index ≤ _
  calc
    natMultiplyCost 2 index ≤
        1000000000000000000000000000000000000 *
          (encodedListSpace [limit] + 1) := by
      simpa [limit] using raw
    _ ≤ 1000000000000000000000000000000000000 *
          (100 * unit) := by
      simp only [encodedListSpace_cons, encodedListSpace_nil]
      exact Nat.mul_le_mul_left _ limitBits
    _ = 100000000000000000000000000000000000000 * unit := by
      ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem flatMotifCellFieldAtCost_le_quadratic
    (outputField : Fin 2) (values : List Nat) :
    flatMotifCellFieldAtCost 9 1 outputField.val values ≤
      flatMotifIndexSpaceBound values := by
  let index := values[1]?.getD 0
  let offset := 9 + 2 * index
  let unit := flatMotifIndexUnit values
  have unitPositive : 10 ≤ unit := by simp [unit, flatMotifIndexUnit]
  have selectedSpace := flatMotifIndexSelectedSpace_le 1 values
  have selectedSpace' : encodedListSpace [index] ≤
      encodedListSpace values + 1 := by
    simpa [index] using selectedSpace
  have selectedBits' : (Computability.encodeNat index).length + 1 ≤
      encodedListSpace values + 1 := by
    simpa [encodedListSpace_cons] using selectedSpace'
  have selectedUnit : encodedListSpace [index] ≤ unit := by
    dsimp [unit, flatMotifIndexUnit]
    omega
  have selectedBits : (Computability.encodeNat index).length + 1 ≤ unit := by
    simpa [encodedListSpace_cons] using selectedUnit
  have productBits := encodeNat_mul_length_le_sum 2 index
  have offsetBitsRaw := encodeNat_add_length_le_sum 9 (2 * index)
  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
  have nineBits : (Computability.encodeNat 9).length = 4 := by native_decide
  have productSpace : encodedListSpace [2 * index] ≤ 3 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have offsetSpace : encodedListSpace [offset] ≤ 5 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil, offset]
    omega
  have valuesSpace : encodedListSpace values ≤ unit := by
    simp [unit, flatMotifIndexUnit]
  have productCost := flatMotifIndexMultiplyCost_le_unit values
  have getIndexRaw := listCodeGetCost_le_linear 1 values
  have getIndex : getCost 1 values ≤ 20000 * (unit + 1) :=
    getIndexRaw.trans (by gcongr)
  have zeroRaw := listCodeZeroCost_le_linear values
  have addTwoSmall : addConstCost 2 [0] ≤ 1000000 := by native_decide
  have numeralTwo : numeralCost 2 values ≤ 1000000 * (unit + 1) := by
    simp only [numeralCost]
    have zeroBound := zeroRaw.trans (by gcongr)
    omega
  have argumentsRaw := listCodePrependCost_le_of values [2] [index]
    (numeralCost 2 values) (getCost 1 values) unit valuesSpace
    (by simp [unit, flatMotifIndexUnit, encodedListSpace_cons]; omega)
    (by
      simp only [List.headI_cons, encodedListSpace_cons,
        encodedListSpace_nil]
      dsimp [unit, flatMotifIndexUnit]
      omega)
  have argumentsCost : flatMotifIndexProductArgumentsCost 1 values ≤
      10000000 * (unit + 1) := by
    simpa [flatMotifIndexProductArgumentsCost] using argumentsRaw.trans (by
      omega)
  have productCost' : natMultiplyCost 2 index ≤
      100000000000000000000000000000000000000 * unit := by
    simpa [index, unit] using productCost
  have productTotal : flatMotifIndexProductCost 1 values ≤
      flatMotifIndexLinearBound values := by
    change natMultiplyCost 2 index +
      flatMotifIndexProductArgumentsCost 1 values ≤ _
    simp only [flatMotifIndexLinearBound]
    change _ ≤ _ * (unit + 1)
    omega
  have offsetAddRaw := addConstCost_le 9 [2 * index]
  have offsetAdd : addConstCost 9 [2 * index] ≤
      flatMotifIndexLinearBound values := by
    simp only [flatMotifIndexLinearBound]
    change _ ≤ _ * (unit + 1)
    omega
  have offsetCost : flatMotifIndexOffsetCost 9 1 values ≤
      2 * flatMotifIndexLinearBound values := by
    change addConstCost 9 [2 * index] +
      flatMotifIndexProductCost 1 values ≤ _
    omega
  have idRaw : idCost values ≤
      10 * (encodedListSpace values + 1) := by
    have tailSpace := listCodeEncodedListSpace_tail_le (0 :: values)
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp [idCost, tailCost, zeroPrimeCost,
      encodedListSpace_cons, zeroBits] at tailSpace ⊢
    omega
  have idBound : idCost values ≤ flatMotifIndexLinearBound values := by
    simp only [flatMotifIndexLinearBound]
    change _ ≤ _ * (unit + 1)
    omega
  have dropOutputSpace : encodedListSpace (offset :: values) ≤
      6 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at offsetSpace ⊢
    omega
  have dropInputRaw := listCodePrependCost_le_of values [offset] values
    (flatMotifIndexOffsetCost 9 1 values) (idCost values) (6 * unit)
    (by omega) (offsetSpace.trans (by omega)) (by
      simpa only [List.headI_cons] using dropOutputSpace)
  have dropInput : flatMotifIndexDropInputCost 9 1 values ≤
      4 * flatMotifIndexLinearBound values := by
    change prependCost values [offset] values
      (flatMotifIndexOffsetCost 9 1 values) (idCost values) ≤ _
    have overhead : 18 * unit + 2 ≤
        flatMotifIndexLinearBound values := by
      simp only [flatMotifIndexLinearBound]
      change _ ≤ _ * (unit + 1)
      omega
    omega
  have dynamic : dynamicDropCost offset values ≤
      flatMotifIndexLinearBound values := by
    simp only [dynamicDropCost, flatMotifIndexLinearBound]
    change _ ≤ _ * (unit + 1)
    omega
  have suffixCost : flatMotifIndexedSuffixCost 9 1 values ≤
      5 * flatMotifIndexLinearBound values := by
    change dynamicDropCost offset values +
      flatMotifIndexDropInputCost 9 1 values ≤ _
    omega
  have suffixSpace := dynamicDropSpace_drop_le offset values
  have projectionRaw := listCodeGetCost_le_linear outputField.val
    (values.drop offset)
  have projection : getCost outputField.val (values.drop offset) ≤
      flatMotifIndexLinearBound values := projectionRaw.trans (by
        have coefficient : 10000 * (outputField.val + 1) ≤ 20000 := by omega
        have space : encodedListSpace (values.drop offset) + 1 ≤ unit + 1 := by
          omega
        have combined := Nat.mul_le_mul coefficient space
        calc
          10000 * (outputField.val + 1) *
              (encodedListSpace (values.drop offset) + 1) ≤
              20000 * (unit + 1) := combined
          _ ≤ flatMotifIndexLinearBound values := by
            simp only [flatMotifIndexLinearBound]
            change _ ≤ _ * (unit + 1)
            exact Nat.mul_le_mul_right (unit + 1) (by norm_num))
  change getCost outputField.val (values.drop offset) +
      flatMotifIndexedSuffixCost 9 1 values ≤
    flatMotifIndexSpaceBound values
  have linearTotal : getCost outputField.val (values.drop offset) +
      flatMotifIndexedSuffixCost 9 1 values ≤
      6 * flatMotifIndexLinearBound values := by omega
  calc
    getCost outputField.val (values.drop offset) +
        flatMotifIndexedSuffixCost 9 1 values ≤
        6 * flatMotifIndexLinearBound values := linearTotal
    _ ≤ flatMotifIndexSpaceBound values := by
      simp [flatMotifIndexLinearBound, flatMotifIndexSpaceBound,
        unit, flatMotifIndexUnit] at *
      nlinarith

end EvaluatorCodeFits
end PartrecToTM2
end Turing
