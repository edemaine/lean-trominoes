/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedCenterBase
import LeanTrominoes.PartrecFlatPackedCenterCoverageSpace
import LeanTrominoes.PartrecFlatPackedCenterSymmetriesSpace
import LeanTrominoes.PartrecPairSpace
import LeanTrominoes.PartrecPackedNormalizedAtSpace

/-!
# Evaluator-space certificate for flat packed center validity at one base

This file fits the direct phase comparison, the guarded containment and
coverage disjunctions, and their final conjunction at one motif occurrence.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private theorem boolOr_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolOr leftCode rightCode) values
      [(left || right).toNat]
      (boolOrCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolOr leftFit rightFit
  cases left <;> cases right <;> simpa using combined

private theorem boolAnd_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolAnd leftCode rightCode) values
      [(left && right).toNat]
      (boolAndCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolAnd leftFit rightFit
  cases left <;> cases right <;> simpa using combined

private theorem flatPackedCenterBoolAndCost_le_budget
    (values : List Nat) (left right : Bool)
    (leftCost rightCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget) :
    boolAndCost values left.toNat right.toNat leftCost rightCost ≤
      1000 * (budget + 1) := by
  have headSpace :=
    listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  apply boolAndCost_le_budget values left.toNat right.toNat
    leftCost rightCost budget
  · cases left <;> simp
  · cases right <;> simp
  · omega
  · omega
  · rw [← Nat.succ_eq_add_one]
    omega
  · exact leftCostBound
  · exact rightCostBound
  · omega

private theorem flatPackedCenterBoolOrCost_le_budget
    (values : List Nat) (left right : Bool)
    (leftCost rightCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget) :
    boolOrCost values left.toNat right.toNat leftCost rightCost ≤
      1000 * (budget + 1) := by
  have headSpace :=
    listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  apply boolOrCost_le_budget values left.toNat right.toNat
    leftCost rightCost budget
  · cases left <;> simp
  · cases right <;> simp
  · omega
  · omega
  · rw [← Nat.succ_eq_add_one]
    omega
  · exact leftCostBound
  · exact rightCostBound
  · omega

private theorem flatPackedCenterIsZeroBoolCost_le_budget
    (values : List Nat) (value : Bool)
    (valueCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (valueCostBound : valueCost ≤ budget)
    (budgetLarge : 100 ≤ budget) :
    isZeroCost values value.toNat valueCost ≤
      1000 * (budget + 1) := by
  have headSpace :=
    listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  apply isZeroCost_le_budget values value.toNat valueCost budget
  · omega
  · cases value <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  · cases value <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits] <;> omega
  · omega
  · rw [← Nat.succ_eq_add_one]
    omega
  · exact valueCostBound
  · omega

def flatPackedCenterBaseCellArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  prependCost values [Encodable.encode base.1] [Encodable.encode base.2]
    (getCost 3 values) (getCost 4 values)

def flatPackedCenterBaseCellCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  natPairCost (Encodable.encode base.1) (Encodable.encode base.2) +
    flatPackedCenterBaseCellArgumentsCost periodicStrip packed base

theorem flatPackedCenterBaseCell
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.flatPackedCenterBaseCellCode
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [Encodable.encode base]
      (flatPackedCenterBaseCellCost periodicStrip packed base) := by
  have baseEncoding : Encodable.encode base =
      Nat.pair (Encodable.encode base.1) (Encodable.encode base.2) := by
    rcases base with ⟨x, y⟩
    rfl
  have arguments := prepend
    (get 3 (Code.flatPackedCenterCandidateInput periodicStrip packed base))
    (get 4 (Code.flatPackedCenterCandidateInput periodicStrip packed base))
  have result := comp
    (natPair (Encodable.encode base.1) (Encodable.encode base.2)) arguments
  simpa [Code.flatPackedCenterBaseCellCode,
    flatPackedCenterBaseCellArgumentsCost,
    flatPackedCenterBaseCellCost,
    Code.flatPackedCenterCandidateInput, prependCost,
    baseEncoding] using result

def flatPackedCenterBaseCoordinateArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let restWord := prependCost values [Encodable.encode base]
    [packed.assignmentWord]
    (flatPackedCenterBaseCellCost periodicStrip packed base)
    (getCost 5 values)
  let restColumn := prependCost values [WindowState.center.val]
    [Encodable.encode base, packed.assignmentWord]
    (numeralCost WindowState.center.val values) restWord
  let restMotif := prependCost values [0]
    [WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    (zeroCost values) restColumn
  let restPhase := prependCost values [packed.phase]
    [0,
      WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    (getCost 1 values) restMotif
  let syntheticPeriodCost := succCost [packed.phase] + getCost 1 values
  prependCost values [packed.phase + 1]
    [packed.phase, 0,
      WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    syntheticPeriodCost restPhase

theorem flatPackedCenterBaseCoordinateArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.flatPackedCenterBaseCoordinateArgumentsCode
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [packed.phase + 1, packed.phase,
        0,
        WindowState.center.val, Encodable.encode base,
        packed.assignmentWord]
      (flatPackedCenterBaseCoordinateArgumentsCost
        periodicStrip packed base) := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  have restWord := prepend
    (flatPackedCenterBaseCell periodicStrip packed base) (get 5 values)
  have restColumn := prepend
    (numeral WindowState.center.val values) restWord
  have restMotif := prepend (zero values) restColumn
  have restPhase := prepend (get 1 values) restMotif
  have syntheticPeriod := comp (succ_named [packed.phase]) (get 1 values)
  simpa [Code.flatPackedCenterBaseCoordinateArgumentsCode,
    flatPackedCenterBaseCoordinateArgumentsCost,
    Code.flatPackedCenterCandidateInput,
    Code.numeral, numeralCost, prependCost, values] using
    prepend syntheticPeriod restPhase

def flatPackedCenterBaseCoordinateArgumentsLinearCoefficient : Nat := 10 ^ 100

theorem flatPackedCenterBaseCoordinateArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseCoordinateArgumentsCost periodicStrip packed base ≤
      flatPackedCenterBaseCoordinateArgumentsLinearCoefficient *
        flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let unit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have get1 := listCodeGetCost_le_linear 1 values
  have get3 := listCodeGetCost_le_linear 3 values
  have get4 := listCodeGetCost_le_linear 4 values
  have get5 := listCodeGetCost_le_linear 5 values
  have zeroBound := listCodeZeroCost_le_linear values
  have addSmall :
      addConstCost WindowState.center.val [0] ≤ 100000 := by
    native_decide
  have centerBits :
      (Computability.encodeNat WindowState.center.val).length ≤ 100 := by
    native_decide
  have numeralBound :
      numeralCost WindowState.center.val values ≤
        1000000 * unit := by
    simp only [numeralCost]
    dsimp only [unit, values, flatPackedCenterCandidateInputUnit] at *
    omega
  have phaseSuccessorBits :=
    listCodeEncodeNat_succ_length_le packed.phase
  have pairUnit := natPairUnit_le_linear
    (Encodable.encode base.1) (Encodable.encode base.2)
  have pairCost := natPairCost_le_linear
    (Encodable.encode base.1) (Encodable.encode base.2)
  have pairBits := encodeNat_pair_length_le
    (Encodable.encode base.1) (Encodable.encode base.2)
  have baseEncoding : Encodable.encode base =
      Nat.pair (Encodable.encode base.1) (Encodable.encode base.2) := by
    rcases base with ⟨x, y⟩
    rfl
  have coordinateBits :
      (Computability.encodeNat (Encodable.encode base.1)).length +
          (Computability.encodeNat (Encodable.encode base.2)).length + 1 ≤
        unit := by
    simp [unit, flatPackedCenterCandidateInputUnit,
      Code.flatPackedCenterCandidateInput, encodedListSpace_cons]
    omega
  have pairUnitGlobal :
      natPairUnit (Encodable.encode base.1) (Encodable.encode base.2) ≤
        100 * unit :=
    pairUnit.trans (Nat.mul_le_mul_left _ coordinateBits)
  have pairCostGlobal :
      natPairCost (Encodable.encode base.1) (Encodable.encode base.2) ≤
        1000000000000000000000000000000000000000000 * unit := by
    calc
      _ ≤ 10000000000000000000000000000000000000000 *
          natPairUnit (Encodable.encode base.1)
            (Encodable.encode base.2) := pairCost
      _ ≤ 10000000000000000000000000000000000000000 *
          (100 * unit) := Nat.mul_le_mul_left _ pairUnitGlobal
      _ = _ := by ring
  have inputSpace : encodedListSpace values + 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit, values]
  have unitLarge : 10 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit]
  have get1Global : getCost 1 values ≤ 100000 * unit := by omega
  have get3Global : getCost 3 values ≤ 100000 * unit := by omega
  have get4Global : getCost 4 values ≤ 100000 * unit := by omega
  have get5Global : getCost 5 values ≤ 100000 * unit := by omega
  have zeroGlobal : zeroCost values ≤ 10000 * unit := by omega
  have successorRaw := succCost_le [packed.phase]
  have phaseSpace : encodedListSpace [packed.phase] + 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit,
      Code.flatPackedCenterCandidateInput, encodedListSpace_cons]
    omega
  have successorGlobal : succCost [packed.phase] ≤ 100 * unit :=
    successorRaw.trans (Nat.mul_le_mul_left _ phaseSpace)
  have phaseBitsGlobal :
      (Computability.encodeNat packed.phase).length ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit,
      Code.flatPackedCenterCandidateInput, encodedListSpace_cons]
    omega
  have phaseSuccBitsGlobal :
      (Computability.encodeNat (packed.phase + 1)).length ≤ 2 * unit := by
    have phaseSuccessorBits' :
        (Computability.encodeNat (packed.phase + 1)).length ≤
          (Computability.encodeNat packed.phase).length + 1 := by
      simpa [Nat.succ_eq_add_one] using phaseSuccessorBits
    omega
  have wordBitsGlobal :
      (Computability.encodeNat packed.assignmentWord).length ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit,
      Code.flatPackedCenterCandidateInput, encodedListSpace_cons]
    omega
  have pairBitsGlobal :
      (Computability.encodeNat
        (Nat.pair (Encodable.encode base.1)
          (Encodable.encode base.2))).length ≤ 3 * unit := by
    omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp only [values] at inputSpace get1Global get3Global get4Global get5Global
  simp only [values] at zeroGlobal numeralBound
  change flatPackedCenterBaseCoordinateArgumentsCost
      periodicStrip packed base ≤
    flatPackedCenterBaseCoordinateArgumentsLinearCoefficient * unit
  simp [flatPackedCenterBaseCoordinateArgumentsCost,
    flatPackedCenterBaseCellCost,
    flatPackedCenterBaseCellArgumentsCost,
    prependCost,
    encodedListSpace_cons, encodedListSpace_nil,
    baseEncoding, zeroBits]
  rw [flatPackedCenterBaseCoordinateArgumentsLinearCoefficient]
  omega

def flatPackedCenterBasePhaseEqualCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedNormalizedAtCoordinateCost
      (packed.phase + 1) packed.phase []
      WindowState.center.val base packed.assignmentWord +
    flatPackedCenterBaseCoordinateArgumentsCost
      periodicStrip packed base

theorem flatPackedCenterBasePhaseEqual
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    let equal := decide (base.1 = (packed.phase : Int))
    EvaluatorCodeFits Code.flatPackedCenterBasePhaseEqualCode
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [equal.toNat]
      (flatPackedCenterBasePhaseEqualCost periodicStrip packed base) := by
  simp only
  let nonnegative :=
    if IntEncoding.sign base.1 = 0 then 1 else 0
  let magnitudeEqual :=
    if IntEncoding.magnitude base.1 = packed.phase then 1 else 0
  have coordinate := packedNormalizedAtCoordinate
    (packed.phase + 1) packed.phase []
    WindowState.center.val base packed.assignmentWord
  simp only [Code.packedCenterSyntheticPhase_eq] at coordinate
  change EvaluatorCodeFits Code.packedNormalizedAtCoordinateCode _
    [if nonnegative = 0 ∨ magnitudeEqual = 0 then 0 else 1] _
    at coordinate
  have rawTagEq :
      (if nonnegative = 0 ∨ magnitudeEqual = 0 then 0 else 1) =
        (decide (base.1 = (packed.phase : Int))).toNat := by
    have tag := Code.packedNormalizedAtCoordinateTag_eq
      (packed.phase + 1) packed.phase WindowState.center.val base
    rw [Code.packedCenterSyntheticPhase_eq] at tag
    simpa [nonnegative, magnitudeEqual] using tag
  rw [rawTagEq] at coordinate
  simpa [Code.flatPackedCenterBasePhaseEqualCode,
    flatPackedCenterBasePhaseEqualCost] using
    comp coordinate
      (flatPackedCenterBaseCoordinateArguments periodicStrip packed base)

def flatPackedCenterBasePhaseEqualSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedNormalizedAtSpaceBound (packed.phase + 1) packed.phase
      0 WindowState.center.val
      (Encodable.encode base) packed.assignmentWord +
    flatPackedCenterBaseCoordinateArgumentsLinearCoefficient *
      flatPackedCenterCandidateInputUnit periodicStrip packed base

theorem flatPackedCenterBasePhaseEqualCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBasePhaseEqualCost periodicStrip packed base ≤
      flatPackedCenterBasePhaseEqualSpaceBound periodicStrip packed base := by
  exact Nat.add_le_add
    (packedNormalizedAtCoordinateCost_le_linear
      (packed.phase + 1) packed.phase []
      WindowState.center.val base packed.assignmentWord)
    (flatPackedCenterBaseCoordinateArgumentsCost_le_linear
      periodicStrip packed base)

def flatPackedCenterBasePhaseEqualLinearCoefficient : Nat :=
  (1000000000000000000000000000000 * 100) * 10 +
    flatPackedCenterBaseCoordinateArgumentsLinearCoefficient

set_option maxRecDepth 100000 in
theorem flatPackedCenterBasePhaseEqualSpaceBound_le_input
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBasePhaseEqualSpaceBound periodicStrip packed base ≤
      flatPackedCenterBasePhaseEqualLinearCoefficient *
        flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  let normalizedInput := packedNormalizedAtInputUnit
    (packed.phase + 1) packed.phase
    0 WindowState.center.val
    (Encodable.encode base) packed.assignmentWord
  let centerInput :=
    flatPackedCenterCandidateInputUnit periodicStrip packed base
  have phaseSucc := encodeNat_add_length_le_sum packed.phase 1
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have centerBits :
      (Computability.encodeNat WindowState.center.val).length = 2 := by
    native_decide
  have pairBits := encodeNat_pair_length_le
    (Encodable.encode base.1) (Encodable.encode base.2)
  have baseEncoding : Encodable.encode base =
      Nat.pair (Encodable.encode base.1) (Encodable.encode base.2) := by
    rcases base with ⟨x, y⟩
    rfl
  have inputBound : normalizedInput ≤ 10 * centerInput := by
    simp [normalizedInput, centerInput,
      packedNormalizedAtInputUnit, flatPackedCenterCandidateInputUnit,
      Code.flatPackedCenterCandidateInput, encodedListSpace_cons,
      encodedListSpace_nil, baseEncoding, zeroBits]
    omega
  have normalized := packedNormalizedAtSpaceBound_le_linear
    (packed.phase + 1) packed.phase
    0 WindowState.center.val
    (Encodable.encode base) packed.assignmentWord
  have normalizedGlobal :
      packedNormalizedAtSpaceBound (packed.phase + 1) packed.phase
          0 WindowState.center.val
          (Encodable.encode base) packed.assignmentWord ≤
        ((1000000000000000000000000000000 * 100) * 10) *
          centerInput := by
    calc
      _ ≤ (1000000000000000000000000000000 * 100) *
            normalizedInput := normalized
      _ ≤ (1000000000000000000000000000000 * 100) *
            (10 * centerInput) := Nat.mul_le_mul_left _ inputBound
      _ = ((1000000000000000000000000000000 * 100) * 10) *
            centerInput := (Nat.mul_assoc _ _ _).symm
  change
    packedNormalizedAtSpaceBound (packed.phase + 1) packed.phase
          0 WindowState.center.val
          (Encodable.encode base) packed.assignmentWord +
        flatPackedCenterBaseCoordinateArgumentsLinearCoefficient *
          centerInput ≤
      flatPackedCenterBasePhaseEqualLinearCoefficient * centerInput
  calc
    _ ≤ ((1000000000000000000000000000000 * 100) * 10) *
          centerInput +
        flatPackedCenterBaseCoordinateArgumentsLinearCoefficient *
          centerInput :=
      Nat.add_le_add_right normalizedGlobal _
    _ = _ := by
      rw [flatPackedCenterBasePhaseEqualLinearCoefficient]
      ring

private theorem flatPackedCenterOneChildSpaceBound_le_input
    (scale child coefficient input : Nat)
    (inputPositive : 1 ≤ input)
    (childBound : child ≤ coefficient * input) :
    scale * (child + input + 100 + 1) ≤
      (scale * (coefficient + 102)) * input := by
  have constantsBound : 101 ≤ 101 * input := by
    simpa using Nat.mul_le_mul_left 101 inputPositive
  have sumBound : child + input + 100 + 1 ≤
      (coefficient + 102) * input := by
    calc
      _ ≤ coefficient * input + input + 100 + 1 := by omega
      _ = (coefficient + 1) * input + 101 := by ring
      _ ≤ (coefficient + 1) * input + 101 * input :=
        Nat.add_le_add_left constantsBound _
      _ = (coefficient + 102) * input := by ring
  calc
    _ ≤ scale * ((coefficient + 102) * input) :=
      Nat.mul_le_mul_left _ sumBound
    _ = _ := (Nat.mul_assoc _ _ _).symm

private theorem flatPackedCenterTwoChildSpaceBound_le_input
    (scale first second firstCoefficient secondCoefficient input : Nat)
    (inputPositive : 1 ≤ input)
    (firstBound : first ≤ firstCoefficient * input)
    (secondBound : second ≤ secondCoefficient * input) :
    scale * (first + second + input + 100 + 1) ≤
      (scale * (firstCoefficient + secondCoefficient + 102)) * input := by
  have constantsBound : 101 ≤ 101 * input := by
    simpa using Nat.mul_le_mul_left 101 inputPositive
  have sumBound : first + second + input + 100 + 1 ≤
      (firstCoefficient + secondCoefficient + 102) * input := by
    calc
      _ ≤ firstCoefficient * input + secondCoefficient * input +
            input + 100 + 1 := by omega
      _ = (firstCoefficient + secondCoefficient + 1) * input + 101 := by
        ring
      _ ≤ (firstCoefficient + secondCoefficient + 1) * input +
            101 * input := Nat.add_le_add_left constantsBound _
      _ = (firstCoefficient + secondCoefficient + 102) * input := by ring
  calc
    _ ≤ scale *
          ((firstCoefficient + secondCoefficient + 102) * input) :=
      Nat.mul_le_mul_left _ sumBound
    _ = _ := (Nat.mul_assoc _ _ _).symm

private theorem flatPackedCenterTwoChildSpaceBound_le_quadratic
    (scale first second firstCoefficient secondCoefficient input : Nat)
    (inputPositive : 1 ≤ input)
    (firstBound : first ≤ firstCoefficient * input ^ 2)
    (secondBound : second ≤ secondCoefficient * input ^ 2) :
    scale * (first + second + input + 100 + 1) ≤
      (scale * (firstCoefficient + secondCoefficient + 102)) * input ^ 2 := by
  have inputQuadratic : input ≤ input ^ 2 := by nlinarith
  have squarePositive : 1 ≤ input ^ 2 := by nlinarith
  have constantsBound : 101 ≤ 101 * input ^ 2 := by
    simpa using Nat.mul_le_mul_left 101 squarePositive
  have sumBound : first + second + input + 100 + 1 ≤
      (firstCoefficient + secondCoefficient + 102) * input ^ 2 := by
    calc
      _ ≤ firstCoefficient * input ^ 2 + secondCoefficient * input ^ 2 +
            input + 100 + 1 := by omega
      _ ≤ firstCoefficient * input ^ 2 + secondCoefficient * input ^ 2 +
            input ^ 2 + 101 * input ^ 2 := by omega
      _ = (firstCoefficient + secondCoefficient + 102) * input ^ 2 := by
        ring
  calc
    _ ≤ scale *
          ((firstCoefficient + secondCoefficient + 102) * input ^ 2) :=
      Nat.mul_le_mul_left _ sumBound
    _ = _ := by ring

def flatPackedCenterBasePhaseDifferentCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let equal := decide (base.1 = (packed.phase : Int))
  isZeroCost values equal.toNat
    (flatPackedCenterBasePhaseEqualCost periodicStrip packed base)

theorem flatPackedCenterBasePhaseDifferent
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.flatPackedCenterBasePhaseDifferentCode
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(decide (base.1 ≠ (packed.phase : Int))).toNat]
      (flatPackedCenterBasePhaseDifferentCost
        periodicStrip packed base) := by
  let equal := decide (base.1 = (packed.phase : Int))
  have equalFit :
      EvaluatorCodeFits Code.flatPackedCenterBasePhaseEqualCode
        (Code.flatPackedCenterCandidateInput periodicStrip packed base)
        [equal.toNat]
        (flatPackedCenterBasePhaseEqualCost periodicStrip packed base) := by
    simpa [equal] using flatPackedCenterBasePhaseEqual
      periodicStrip packed base
  have result := isZero equalFit
  by_cases equality : base.1 = (packed.phase : Int)
  · simpa [Code.flatPackedCenterBasePhaseDifferentCode,
      flatPackedCenterBasePhaseDifferentCost, equal, equality] using result
  · simpa [Code.flatPackedCenterBasePhaseDifferentCode,
      flatPackedCenterBasePhaseDifferentCost, equal, equality] using result

def flatPackedCenterBasePhaseDifferentSpaceUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterBasePhaseEqualSpaceBound periodicStrip packed base +
    flatPackedCenterCandidateInputUnit periodicStrip packed base + 100

def flatPackedCenterBasePhaseDifferentSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (flatPackedCenterBasePhaseDifferentSpaceUnit
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem flatPackedCenterBasePhaseDifferentCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBasePhaseDifferentCost periodicStrip packed base ≤
      flatPackedCenterBasePhaseDifferentSpaceBound
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let equal := decide (base.1 = (packed.phase : Int))
  let equalCost := flatPackedCenterBasePhaseEqualCost
    periodicStrip packed base
  let budget := flatPackedCenterBasePhaseDifferentSpaceUnit
    periodicStrip packed base
  apply flatPackedCenterIsZeroBoolCost_le_budget
  · simp only [budget, flatPackedCenterBasePhaseDifferentSpaceUnit,
      flatPackedCenterCandidateInputUnit, values]
    omega
  · have bound := flatPackedCenterBasePhaseEqualCost_le_linear
      periodicStrip packed base
    simp only [equalCost, budget,
      flatPackedCenterBasePhaseDifferentSpaceUnit]
    omega
  · simp only [budget, flatPackedCenterBasePhaseDifferentSpaceUnit]
    omega

def flatPackedCenterBasePhaseDifferentLinearCoefficient : Nat :=
  1000 * (flatPackedCenterBasePhaseEqualLinearCoefficient + 102)

set_option maxRecDepth 100000 in
theorem flatPackedCenterBasePhaseDifferentSpaceBound_le_input
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base ≤
      flatPackedCenterBasePhaseDifferentLinearCoefficient *
        flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have positive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have child := flatPackedCenterBasePhaseEqualSpaceBound_le_input
    periodicStrip packed base
  change
    1000 *
        (flatPackedCenterBasePhaseEqualSpaceBound periodicStrip packed base +
          input + 100 + 1) ≤
      (1000 * (flatPackedCenterBasePhaseEqualLinearCoefficient + 102)) * input
  exact flatPackedCenterOneChildSpaceBound_le_input 1000
    (flatPackedCenterBasePhaseEqualSpaceBound periodicStrip packed base)
    flatPackedCenterBasePhaseEqualLinearCoefficient input positive child

def flatPackedCenterBaseInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  boolOrCost values different.toNat inside.toNat
    (flatPackedCenterBasePhaseDifferentCost periodicStrip packed base)
    (flatPackedCenterAllSymmetriesInsideCost tromino
      periodicStrip packed base)

theorem flatPackedCenterBaseInside
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.flatPackedCenterBaseInsideCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.centerBaseInsideBool
        tromino periodicStrip base).toNat]
      (flatPackedCenterBaseInsideCost tromino
        periodicStrip packed base) := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  have result := boolOr_fit_bool different inside
    (by
      simpa [different] using
        (flatPackedCenterBasePhaseDifferent periodicStrip packed base))
    (by
      simpa [inside] using
        (flatPackedCenterAllSymmetriesInside tromino periodicStrip
          wellFormed packed base))
  simpa [Code.flatPackedCenterBaseInsideCode,
    flatPackedCenterBaseInsideCost,
    PackedWindowState.centerBaseInsideBool,
    different, inside] using result

def flatPackedCenterBaseInsideSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base +
    flatPackedCenterAllSymmetriesInsideSpaceBound tromino
      periodicStrip packed base +
    flatPackedCenterCandidateInputUnit periodicStrip packed base + 100

def flatPackedCenterBaseInsideSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (flatPackedCenterBaseInsideSpaceUnit tromino
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem flatPackedCenterBaseInsideCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseInsideCost tromino periodicStrip packed base ≤
      flatPackedCenterBaseInsideSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  let differentCost := flatPackedCenterBasePhaseDifferentCost
    periodicStrip packed base
  let insideCost := flatPackedCenterAllSymmetriesInsideCost tromino
    periodicStrip packed base
  let budget := flatPackedCenterBaseInsideSpaceUnit tromino
    periodicStrip packed base
  apply flatPackedCenterBoolOrCost_le_budget
  · simp only [budget, flatPackedCenterBaseInsideSpaceUnit,
      flatPackedCenterCandidateInputUnit, values]
    omega
  · have bound := flatPackedCenterBasePhaseDifferentCost_le_linear
      periodicStrip packed base
    simp only [differentCost, budget, flatPackedCenterBaseInsideSpaceUnit]
    omega
  · have bound := flatPackedCenterAllSymmetriesInsideCost_le_linear
      tromino periodicStrip packed base
    simp only [insideCost, budget, flatPackedCenterBaseInsideSpaceUnit]
    omega

def flatPackedCenterBaseInsideQuadraticCoefficient : Nat :=
  1000 * (flatPackedCenterBasePhaseDifferentLinearCoefficient +
    flatPackedCenterAllSymmetriesInsideQuadraticCoefficient + 102)

set_option maxRecDepth 100000 in
theorem flatPackedCenterBaseInsideSpaceBound_le_quadratic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseInsideSpaceBound tromino periodicStrip packed base ≤
      flatPackedCenterBaseInsideQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have positive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have firstLinear := flatPackedCenterBasePhaseDifferentSpaceBound_le_input
    periodicStrip packed base
  have inputQuadratic : input ≤ input ^ 2 := by nlinarith
  have first :
      flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base ≤
        flatPackedCenterBasePhaseDifferentLinearCoefficient * input ^ 2 :=
    firstLinear.trans (Nat.mul_le_mul_left _ inputQuadratic)
  have second := flatPackedCenterAllSymmetriesInsideSpaceBound_le_quadratic
    tromino periodicStrip packed base
  change
    1000 *
        (flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base +
          flatPackedCenterAllSymmetriesInsideSpaceBound tromino
            periodicStrip packed base + input + 100 + 1) ≤
      (1000 * (flatPackedCenterBasePhaseDifferentLinearCoefficient +
        flatPackedCenterAllSymmetriesInsideQuadraticCoefficient + 102)) *
          input ^ 2
  exact flatPackedCenterTwoChildSpaceBound_le_quadratic 1000
    (flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base)
    (flatPackedCenterAllSymmetriesInsideSpaceBound tromino
      periodicStrip packed base)
    flatPackedCenterBasePhaseDifferentLinearCoefficient
    flatPackedCenterAllSymmetriesInsideQuadraticCoefficient input positive
    first second

def flatPackedCenterBaseCoveredCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  boolOrCost values different.toNat covered.toNat
    (flatPackedCenterBasePhaseDifferentCost periodicStrip packed base)
    (flatPackedCenterExactlyOneCoveringCost tromino
      periodicStrip packed base)

theorem flatPackedCenterBaseCovered
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.flatPackedCenterBaseCoveredCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.centerBaseCoveredBool
        tromino periodicStrip base).toNat]
      (flatPackedCenterBaseCoveredCost tromino
        periodicStrip packed base) := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  have result := boolOr_fit_bool different covered
    (by
      simpa [different] using
        (flatPackedCenterBasePhaseDifferent periodicStrip packed base))
    (by
      simpa [covered] using
        (flatPackedCenterExactlyOneCovering
          tromino periodicStrip packed base))
  simpa [Code.flatPackedCenterBaseCoveredCode,
    flatPackedCenterBaseCoveredCost,
    PackedWindowState.centerBaseCoveredBool,
    different, covered] using result

def flatPackedCenterBaseCoveredSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base +
    flatPackedCenterExactlyOneCoveringSpaceBound tromino
      periodicStrip packed base +
    flatPackedCenterCandidateInputUnit periodicStrip packed base + 100

def flatPackedCenterBaseCoveredSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (flatPackedCenterBaseCoveredSpaceUnit tromino
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem flatPackedCenterBaseCoveredCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseCoveredCost tromino periodicStrip packed base ≤
      flatPackedCenterBaseCoveredSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  let differentCost := flatPackedCenterBasePhaseDifferentCost
    periodicStrip packed base
  let coveredCost := flatPackedCenterExactlyOneCoveringCost tromino
    periodicStrip packed base
  let budget := flatPackedCenterBaseCoveredSpaceUnit tromino
    periodicStrip packed base
  apply flatPackedCenterBoolOrCost_le_budget
  · simp only [budget, flatPackedCenterBaseCoveredSpaceUnit,
      flatPackedCenterCandidateInputUnit, values]
    omega
  · have bound := flatPackedCenterBasePhaseDifferentCost_le_linear
      periodicStrip packed base
    simp only [differentCost, budget,
      flatPackedCenterBaseCoveredSpaceUnit]
    omega
  · have bound := flatPackedCenterExactlyOneCoveringCost_le_bound
      tromino periodicStrip packed base
    simp only [coveredCost, budget, flatPackedCenterBaseCoveredSpaceUnit]
    omega

def flatPackedCenterBaseCoveredQuadraticCoefficient (tromino : Tromino) : Nat :=
  1000 * (flatPackedCenterBasePhaseDifferentLinearCoefficient +
    flatPackedCenterExactlyOneCoveringQuadraticCoefficient tromino + 102)

set_option maxRecDepth 100000 in
theorem flatPackedCenterBaseCoveredSpaceBound_le_quadratic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseCoveredSpaceBound tromino periodicStrip packed base ≤
      flatPackedCenterBaseCoveredQuadraticCoefficient tromino *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have positive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have firstLinear := flatPackedCenterBasePhaseDifferentSpaceBound_le_input
    periodicStrip packed base
  have inputQuadratic : input ≤ input ^ 2 := by nlinarith
  have first :
      flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base ≤
        flatPackedCenterBasePhaseDifferentLinearCoefficient * input ^ 2 :=
    firstLinear.trans (Nat.mul_le_mul_left _ inputQuadratic)
  have second := flatPackedCenterExactlyOneCoveringSpaceBound_le_quadratic
    tromino periodicStrip packed base
  change
    1000 *
        (flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base +
          flatPackedCenterExactlyOneCoveringSpaceBound tromino
            periodicStrip packed base + input + 100 + 1) ≤
      (1000 * (flatPackedCenterBasePhaseDifferentLinearCoefficient +
        flatPackedCenterExactlyOneCoveringQuadraticCoefficient tromino + 102)) *
          input ^ 2
  exact flatPackedCenterTwoChildSpaceBound_le_quadratic 1000
    (flatPackedCenterBasePhaseDifferentSpaceBound periodicStrip packed base)
    (flatPackedCenterExactlyOneCoveringSpaceBound tromino
      periodicStrip packed base)
    flatPackedCenterBasePhaseDifferentLinearCoefficient
    (flatPackedCenterExactlyOneCoveringQuadraticCoefficient tromino) input positive
    first second

def flatPackedCenterBaseValidCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  boolAndCost values
    (packed.centerBaseInsideBool tromino periodicStrip base).toNat
    (packed.centerBaseCoveredBool tromino periodicStrip base).toNat
    (flatPackedCenterBaseInsideCost tromino periodicStrip packed base)
    (flatPackedCenterBaseCoveredCost tromino periodicStrip packed base)

def flatPackedCenterBaseValidSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterBaseInsideSpaceBound tromino periodicStrip packed base +
    flatPackedCenterBaseCoveredSpaceBound tromino periodicStrip packed base +
    flatPackedCenterCandidateInputUnit periodicStrip packed base + 100

def flatPackedCenterBaseValidSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (flatPackedCenterBaseValidSpaceUnit tromino
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem flatPackedCenterBaseValidCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseValidCost tromino periodicStrip packed base ≤
      flatPackedCenterBaseValidSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let inside := packed.centerBaseInsideBool tromino periodicStrip base
  let covered := packed.centerBaseCoveredBool tromino periodicStrip base
  let insideCost := flatPackedCenterBaseInsideCost tromino
    periodicStrip packed base
  let coveredCost := flatPackedCenterBaseCoveredCost tromino
    periodicStrip packed base
  let budget := flatPackedCenterBaseValidSpaceUnit tromino
    periodicStrip packed base
  apply flatPackedCenterBoolAndCost_le_budget
  · simp only [budget, flatPackedCenterBaseValidSpaceUnit,
      flatPackedCenterCandidateInputUnit, values]
    omega
  · have bound := flatPackedCenterBaseInsideCost_le_linear
      tromino periodicStrip packed base
    simp only [insideCost, budget, flatPackedCenterBaseValidSpaceUnit]
    omega
  · have bound := flatPackedCenterBaseCoveredCost_le_linear
      tromino periodicStrip packed base
    simp only [coveredCost, budget, flatPackedCenterBaseValidSpaceUnit]
    omega

def flatPackedCenterBaseValidQuadraticCoefficient (tromino : Tromino) : Nat :=
  1000 * (flatPackedCenterBaseInsideQuadraticCoefficient +
    flatPackedCenterBaseCoveredQuadraticCoefficient tromino + 102)

set_option maxRecDepth 100000 in
theorem flatPackedCenterBaseValidSpaceBound_le_quadratic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterBaseValidSpaceBound tromino periodicStrip packed base ≤
      flatPackedCenterBaseValidQuadraticCoefficient tromino *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have positive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have first := flatPackedCenterBaseInsideSpaceBound_le_quadratic
    tromino periodicStrip packed base
  have second := flatPackedCenterBaseCoveredSpaceBound_le_quadratic
    tromino periodicStrip packed base
  change
    1000 *
        (flatPackedCenterBaseInsideSpaceBound tromino periodicStrip packed base +
          flatPackedCenterBaseCoveredSpaceBound tromino periodicStrip packed base +
          input + 100 + 1) ≤
      (1000 * (flatPackedCenterBaseInsideQuadraticCoefficient +
        flatPackedCenterBaseCoveredQuadraticCoefficient tromino + 102)) *
          input ^ 2
  exact flatPackedCenterTwoChildSpaceBound_le_quadratic 1000
    (flatPackedCenterBaseInsideSpaceBound tromino periodicStrip packed base)
    (flatPackedCenterBaseCoveredSpaceBound tromino periodicStrip packed base)
    flatPackedCenterBaseInsideQuadraticCoefficient
    (flatPackedCenterBaseCoveredQuadraticCoefficient tromino) input positive
    first second

/-- Exact fitted execution of both center conditions at one motif base. -/
theorem flatPackedCenterBaseValid
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.flatPackedCenterBaseValidCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [((packed.centerBaseInsideBool tromino periodicStrip base) &&
        packed.centerBaseCoveredBool tromino periodicStrip base).toNat]
      (flatPackedCenterBaseValidCost tromino
        periodicStrip packed base) := by
  simpa [Code.flatPackedCenterBaseValidCode,
    flatPackedCenterBaseValidCost] using
    boolAnd_fit_bool
      (packed.centerBaseInsideBool tromino periodicStrip base)
      (packed.centerBaseCoveredBool tromino periodicStrip base)
      (flatPackedCenterBaseInside tromino periodicStrip
        wellFormed packed base)
      (flatPackedCenterBaseCovered tromino periodicStrip packed base)

theorem flatPackedCenterBaseValidPolynomialBounded
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.flatPackedCenterBaseValidCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [((packed.centerBaseInsideBool tromino periodicStrip base) &&
        packed.centerBaseCoveredBool tromino periodicStrip base).toNat]
      (flatPackedCenterBaseValidQuadraticCoefficient tromino *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2) :=
  (flatPackedCenterBaseValid tromino periodicStrip wellFormed packed base).mono
    ((flatPackedCenterBaseValidCost_le_linear tromino periodicStrip packed
      base).trans
        (flatPackedCenterBaseValidSpaceBound_le_quadratic tromino
          periodicStrip packed base))

end EvaluatorCodeFits

end PartrecToTM2
end Turing
