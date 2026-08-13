/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFuel
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Evaluator-space certificate for explicit Savitch fuel

The nested countdowns in `PartrecFuel` can take exponential time, but every
arithmetic accumulator is monotone and bounded by the value returned by its
enclosing loop.  This module turns that observation into compositional
evaluator-call certificates.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def fuelIncrementTotalCost (values : List Nat) : Nat :=
  let third := values[2]?.getD 0
  let thirdCost :=
    succCost [third] + getCost 2 values
  let restCost :=
    prependCost values [values[1]?.getD 0] [third + 1]
      (getCost 1 values) thirdCost
  prependCost values [values[0]?.getD 0]
    [values[1]?.getD 0, third + 1]
    (getCost 0 values) restCost

theorem fuelIncrementTotal (values : List Nat) :
    EvaluatorCodeFits Code.fuelIncrementTotalCode values
      (Code.fuelIncrementTotalList values)
      (fuelIncrementTotalCost values) := by
  let third := values[2]?.getD 0
  have thirdFits :=
    comp (succ_named [third]) (get 2 values)
  have restFits :=
    prepend (get 1 values) thirdFits
  have result :=
    prepend (get 0 values) restFits
  simpa [Code.fuelIncrementTotalCode,
    Code.fuelIncrementTotalList, fuelIncrementTotalCost,
    third, prependCost] using result

def fuelAddPreviousInputCost (values : List Nat) : Nat :=
  let fourthCost := getCost 2 values
  let thirdCost :=
    prependCost values [values[1]?.getD 0]
      [values[2]?.getD 0]
      (getCost 1 values) fourthCost
  let secondCost :=
    prependCost values [values[0]?.getD 0]
      [values[1]?.getD 0, values[2]?.getD 0]
      (getCost 0 values) thirdCost
  prependCost values [values[1]?.getD 0]
    [values[0]?.getD 0, values[1]?.getD 0,
      values[2]?.getD 0]
    (getCost 1 values) secondCost

theorem fuelAddPreviousInput (values : List Nat) :
    EvaluatorCodeFits Code.fuelAddPreviousInputCode values
      [values[1]?.getD 0, values[0]?.getD 0,
        values[1]?.getD 0, values[2]?.getD 0]
      (fuelAddPreviousInputCost values) := by
  have fourth := get 2 values
  have third := prepend (get 1 values) fourth
  have second := prepend (get 0 values) third
  have result := prepend (get 1 values) second
  simpa [Code.fuelAddPreviousInputCode,
    fuelAddPreviousInputCost, prependCost] using result

def fuelAddTwoCost (values : List Nat) : Nat :=
  let thirdCost :=
    addConstCost 2 [values[2]?.getD 0] +
      getCost 2 values
  let restCost :=
    prependCost values [values[1]?.getD 0]
      [values[2]?.getD 0 + 2]
      (getCost 1 values) thirdCost
  prependCost values [values[0]?.getD 0]
    [values[1]?.getD 0, values[2]?.getD 0 + 2]
    (getCost 0 values) restCost

theorem fuelAddTwo (values : List Nat) :
    EvaluatorCodeFits Code.fuelAddTwoCode values
      [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0 + 2]
      (fuelAddTwoCost values) := by
  have third :=
    comp (addConst 2 [values[2]?.getD 0])
      (get 2 values)
  have rest := prepend (get 1 values) third
  have result := prepend (get 0 values) rest
  simpa [Code.fuelAddTwoCode, fuelAddTwoCost,
    prependCost] using result

def fuelMultiplyInputCost (values : List Nat) : Nat :=
  let fourthCost := oneCost values
  let thirdCost :=
    prependCost values [values[1]?.getD 0] [1]
      (getCost 1 values) fourthCost
  let secondCost :=
    prependCost values [values[0]?.getD 0]
      [values[1]?.getD 0, 1]
      (getCost 0 values) thirdCost
  prependCost values [values[0]?.getD 0]
    [values[0]?.getD 0, values[1]?.getD 0, 1]
    (getCost 0 values) secondCost

theorem fuelMultiplyInput (values : List Nat) :
    EvaluatorCodeFits Code.fuelMultiplyInputCode values
      [values[0]?.getD 0, values[0]?.getD 0,
        values[1]?.getD 0, 1]
      (fuelMultiplyInputCost values) := by
  have fourth := one values
  have third := prepend (get 1 values) fourth
  have second := prepend (get 0 values) third
  have result := prepend (get 0 values) second
  simpa [Code.fuelMultiplyInputCode,
    fuelMultiplyInputCost, prependCost] using result

def fuelStepOutputCost (values : List Nat) : Nat :=
  prependCost values [values[0]?.getD 0]
    [values[2]?.getD 0]
    (getCost 0 values) (getCost 2 values)

theorem fuelStepOutput (values : List Nat) :
    EvaluatorCodeFits Code.fuelStepOutputCode values
      [values[0]?.getD 0, values[2]?.getD 0]
      (fuelStepOutputCost values) := by
  simpa [Code.fuelStepOutputCode,
    fuelStepOutputCost, prependCost] using
    prepend (get 0 values) (get 2 values)

def fuelIncrementBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.fuelIncrementTotalList
    fuelIncrementTotalCost remaining payload

theorem fuelIncrementBody
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.fuelIncrementTotalCode)
      (remaining :: payload)
      (flatCountdownOutput Code.fuelIncrementTotalList
        remaining payload)
      (fuelIncrementBodyCost remaining payload) := by
  simpa [fuelIncrementBodyCost] using
    flatCountdownBody fuelIncrementTotal remaining payload

def fuelAddPreviousLoopCost (values : List Nat) : Nat :=
  1000000000000000 *
    (3 * encodedListSpace
        [values[0]?.getD 0, values[1]?.getD 0,
          values[2]?.getD 0] +
      encodedListSpace
        [values[0]?.getD 0, values[1]?.getD 0,
          values[2]?.getD 0 + values[1]?.getD 0] + 1)

def fuelAddPreviousCost (values : List Nat) : Nat :=
  fuelAddPreviousInputCost values +
    fuelAddPreviousLoopCost values

def FuelAddPreviousInvariant
    (stateCount previous initial remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = previous ∧
      payload = [stateCount, previous, initial + processed]

theorem fuelAddPreviousInvariant_initial
    (stateCount previous initial : Nat) :
    FuelAddPreviousInvariant stateCount previous initial
      previous [stateCount, previous, initial] := by
  exact ⟨0, by simp, by simp⟩

theorem fuelAddPreviousInvariant_preserved
    (stateCount previous initial remaining : Nat)
    (payload : List Nat)
    (invariant :
      FuelAddPreviousInvariant stateCount previous initial
        (remaining + 1) payload) :
    FuelAddPreviousInvariant stateCount previous initial remaining
      (Code.fuelIncrementTotalList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.fuelIncrementTotalList]
  omega

theorem fuelIncrementBodyCost_le_addPreviousLoopCost
    (stateCount previous initial remaining : Nat)
    (payload : List Nat)
    (invariant :
      FuelAddPreviousInvariant stateCount previous initial
        remaining payload) :
    fuelIncrementBodyCost remaining payload ≤
      fuelAddPreviousLoopCost [stateCount, previous, initial] := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have processedBound : processed ≤ previous := by omega
  have currentBound : initial + processed ≤ initial + previous := by
    omega
  have currentBits :=
    encodeNat_length_mono currentBound
  have initialBits :=
    encodeNat_length_mono
      (show initial ≤ initial + previous by omega)
  have stateCountSuccessorBits :=
    encodeNat_succ_length_le stateCount
  have stateCountPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using stateCountSuccessorBits
  have previousSuccessorBits :=
    encodeNat_succ_length_le previous
  have previousPlusBits :
      (Computability.encodeNat (previous + 1)).length ≤
        (Computability.encodeNat previous).length + 1 := by
    simpa [Nat.succ_eq_add_one] using previousSuccessorBits
  have currentSuccessorBits :=
    encodeNat_succ_length_le (initial + processed)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [fuelIncrementBodyCost, flatCountdownBodyCost,
        fuelAddPreviousLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits]
      omega
  | succ remaining =>
      have nextBound :
          initial + processed + 1 ≤ initial + previous := by
        omega
      have nextBits :=
        encodeNat_length_mono nextBound
      have remainingBound : remaining ≤ previous := by omega
      have remainingBits :=
        encodeNat_length_mono remainingBound
      have inputRemainingBound : remaining + 1 ≤ previous := by
        omega
      have inputRemainingBits :=
        encodeNat_length_mono inputRemainingBound
      simp [fuelIncrementBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, fuelIncrementTotalCost,
        fuelAddPreviousLoopCost, prependCost, getCost, dropCost,
        idCost, headCost, nilCost, oneCost, zeroCost,
        zeroPrimeCost, tailCost, succCost,
        Code.fuelIncrementTotalList,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits]
      omega

theorem fuelAddPrevious (values : List Nat) :
    EvaluatorCodeFits Code.fuelAddPreviousCode values
      [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0 + values[1]?.getD 0]
      (fuelAddPreviousCost values) where
  input_space := by
    have inputSpace :=
      (fuelAddPreviousInput values).input_space
    simp only [fuelAddPreviousCost]
    omega
  output_space := by
    simp [fuelAddPreviousCost, fuelAddPreviousLoopCost]
    omega
  call continuation bound budget after := by
    let stateCount := values[0]?.getD 0
    let previous := values[1]?.getD 0
    let initial := values[2]?.getD 0
    have budget' :
        fuelAddPreviousInputCost values +
            fuelAddPreviousLoopCost values +
            continuationSpace continuation ≤
          bound := by
      simpa [fuelAddPreviousCost] using budget
    have finalPayload :
        ((Code.fuelIncrementTotalList)^[previous])
            [stateCount, previous, initial] =
          [stateCount, previous, initial + previous] :=
      Code.fuelIncrementTotalList_iterate
        previous stateCount previous initial
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.fuelIncrementTotalCode)
          continuation
          [previous, stateCount, previous, initial] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := fuelIncrementBodyCost)
          (invariant :=
            FuelAddPreviousInvariant
              stateCount previous initial)
      · exact fuelIncrementBody
      · exact
          fuelAddPreviousInvariant_initial
            stateCount previous initial
      · exact
          fuelAddPreviousInvariant_preserved
            stateCount previous initial
      · intro remaining payload invariant
        have bodyCost :=
          fuelIncrementBodyCost_le_addPreviousLoopCost
            stateCount previous initial remaining payload invariant
        simp only [fuelAddPreviousCost] at budget
        change
          fuelIncrementBodyCost remaining payload ≤
            fuelAddPreviousLoopCost values at bodyCost
        omega
      · rw [finalPayload]
        simpa [stateCount, previous, initial] using after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.fuelIncrementTotalCode)
        continuation
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation
            [previous, stateCount, previous, initial]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        have loopInputSpace :
            encodedListSpace
                [previous, stateCount, previous, initial] ≤
              fuelAddPreviousLoopCost values := by
          simp [fuelAddPreviousLoopCost,
            stateCount, previous, initial]
          omega
        omega
      · exact flatCall
    have inputCall :=
      (fuelAddPreviousInput values).call
        loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp]
          simp only [fuelAddPreviousCost] at budget
          omega)
        (by
          simpa [stateCount, previous, initial] using afterInput)
    have whole := EvaluatorCallFits.comp inputCall
    simpa [Code.fuelAddPreviousCode,
      loopContinuation] using whole

def fuelAddChunkCost (values : List Nat) : Nat :=
  let firstOutput :=
    [values[0]?.getD 0, values[1]?.getD 0,
      values[2]?.getD 0 + values[1]?.getD 0]
  let secondOutput :=
    [values[0]?.getD 0, values[1]?.getD 0,
      values[2]?.getD 0 + values[1]?.getD 0 +
        values[1]?.getD 0]
  fuelAddTwoCost secondOutput +
    fuelAddPreviousCost firstOutput +
      fuelAddPreviousCost values

theorem fuelAddChunk (values : List Nat) :
    EvaluatorCodeFits Code.fuelAddChunkCode values
      (Code.fuelAddChunkList values)
      (fuelAddChunkCost values) := by
  have first := fuelAddPrevious values
  have second :=
    fuelAddPrevious
      [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0 + values[1]?.getD 0]
  have twice := comp second first
  have added :=
    fuelAddTwo
      [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0 + values[1]?.getD 0 +
          values[1]?.getD 0]
  have result := comp added twice
  convert result using 1
  all_goals
    simp [Code.fuelAddChunkCode, Code.fuelAddChunkList,
      fuelAddChunkCost, Nat.add_assoc]
  all_goals omega

def fuelAddChunkBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.fuelAddChunkList
    fuelAddChunkCost remaining payload

theorem fuelAddChunkBody
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.fuelAddChunkCode)
      (remaining :: payload)
      (flatCountdownOutput Code.fuelAddChunkList
        remaining payload)
      (fuelAddChunkBodyCost remaining payload) := by
  simpa [fuelAddChunkBodyCost] using
    flatCountdownBody fuelAddChunk remaining payload

def fuelAddChunkBound
    (stateCount previous total : Nat) : Nat :=
  100000000000000000000 *
    (encodedListSpace [stateCount, previous, total] +
      encodedListSpace
        [stateCount, previous,
          total + (2 * previous + 2)] + 1)

theorem fuelAddChunkCost_le
    (stateCount previous total : Nat) :
    fuelAddChunkCost [stateCount, previous, total] ≤
      fuelAddChunkBound stateCount previous total := by
  let final := total + (2 * previous + 2)
  have totalBound : total ≤ final := by
    simp [final]
  have onceBound : total + previous ≤ final := by
    simp [final]
    omega
  have twiceBound :
      total + previous + previous ≤ final := by
    simp [final]
    omega
  have twicePlusOneBound :
      total + previous + previous + 1 ≤ final := by
    simp [final]
    omega
  have twicePlusTwoBound :
      total + previous + previous + 2 ≤ final := by
    simp [final]
    omega
  have twicePlusOnePlusOneBound :
      total + previous + previous + 1 + 1 ≤ final := by
    omega
  have totalBits := encodeNat_length_mono totalBound
  have onceBits := encodeNat_length_mono onceBound
  have twiceBits := encodeNat_length_mono twiceBound
  have twicePlusOneBits :=
    encodeNat_length_mono twicePlusOneBound
  have twicePlusTwoBits :=
    encodeNat_length_mono twicePlusTwoBound
  have twicePlusOnePlusOneBits :=
    encodeNat_length_mono twicePlusOnePlusOneBound
  have finalBitsEq :
      (Computability.encodeNat
        (total + (2 * previous + 2))).length =
      (Computability.encodeNat final).length := by
    congr 2
  have stateCountSuccessorBits :=
    encodeNat_succ_length_le stateCount
  have stateCountPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using stateCountSuccessorBits
  have previousSuccessorBits :=
    encodeNat_succ_length_le previous
  have previousPlusBits :
      (Computability.encodeNat (previous + 1)).length ≤
        (Computability.encodeNat previous).length + 1 := by
    simpa [Nat.succ_eq_add_one] using previousSuccessorBits
  have totalSuccessorBits :=
    encodeNat_succ_length_le total
  have totalPlusBits :
      (Computability.encodeNat (total + 1)).length ≤
        (Computability.encodeNat total).length + 1 := by
    simpa [Nat.succ_eq_add_one] using totalSuccessorBits
  have onceSuccessorBits :=
    encodeNat_succ_length_le (total + previous)
  have oncePlusBits :
      (Computability.encodeNat
        (total + previous + 1)).length ≤
          (Computability.encodeNat
            (total + previous)).length + 1 := by
    simpa [Nat.succ_eq_add_one] using onceSuccessorBits
  have twiceSuccessorBits :=
    encodeNat_succ_length_le
      (total + previous + previous)
  have twicePlusBits :
      (Computability.encodeNat
        (total + previous + previous + 1)).length ≤
          (Computability.encodeNat
            (total + previous + previous)).length + 1 := by
    simpa [Nat.succ_eq_add_one] using twiceSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [fuelAddChunkCost, fuelAddChunkBound,
    fuelAddPreviousCost, fuelAddPreviousInputCost,
    fuelAddPreviousLoopCost, fuelAddTwoCost,
    prependCost, getCost, dropCost, idCost, headCost,
    nilCost, zeroPrimeCost, tailCost,
    succCost, addConstCost, encodedListSpace_cons,
    encodedListSpace_nil, zeroBits]
  omega

def fuelMultiplyLoopCost (values : List Nat) : Nat :=
  let stateCount := values[0]?.getD 0
  let previous := values[1]?.getD 0
  1000000000000000000000000000000 *
    (3 * encodedListSpace [stateCount, previous, 1] +
      encodedListSpace
        [stateCount, previous,
          1 + stateCount * (2 * previous + 2)] + 1)

def fuelMultiplyCost (values : List Nat) : Nat :=
  fuelMultiplyInputCost values + fuelMultiplyLoopCost values

def FuelMultiplyInvariant
    (stateCount previous remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = stateCount ∧
      payload =
        [stateCount, previous,
          1 + processed * (2 * previous + 2)]

theorem fuelMultiplyInvariant_initial
    (stateCount previous : Nat) :
    FuelMultiplyInvariant stateCount previous stateCount
      [stateCount, previous, 1] := by
  exact ⟨0, by simp, by simp⟩

theorem fuelMultiplyInvariant_preserved
    (stateCount previous remaining : Nat)
    (payload : List Nat)
    (invariant :
      FuelMultiplyInvariant stateCount previous
        (remaining + 1) payload) :
    FuelMultiplyInvariant stateCount previous remaining
      (Code.fuelAddChunkList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.fuelAddChunkList]
  ring

theorem fuelAddChunkBodyCost_le_multiplyLoopCost
    (stateCount previous remaining : Nat)
    (payload : List Nat)
    (invariant :
      FuelMultiplyInvariant stateCount previous
        remaining payload) :
    fuelAddChunkBodyCost remaining payload ≤
      fuelMultiplyLoopCost [stateCount, previous] := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  let chunk := 2 * previous + 2
  let final := 1 + stateCount * chunk
  let current := 1 + processed * chunk
  have processedBound : processed ≤ stateCount := by omega
  have currentBound : current ≤ final := by
    dsimp [current, final]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right chunk processedBound) 1
  have currentBits := encodeNat_length_mono currentBound
  have stateCountSuccessorBits :=
    encodeNat_succ_length_le stateCount
  have stateCountPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using stateCountSuccessorBits
  have previousSuccessorBits :=
    encodeNat_succ_length_le previous
  have previousPlusBits :
      (Computability.encodeNat (previous + 1)).length ≤
        (Computability.encodeNat previous).length + 1 := by
    simpa [Nat.succ_eq_add_one] using previousSuccessorBits
  have currentSuccessorBits :=
    encodeNat_succ_length_le current
  have currentPlusBits :
      (Computability.encodeNat (current + 1)).length ≤
        (Computability.encodeNat current).length + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have currentDirectBits :
      (Computability.encodeNat
        (1 + processed * (2 * previous + 2))).length =
        (Computability.encodeNat current).length := by
    rfl
  have finalDirectBits :
      (Computability.encodeNat
        (1 + stateCount * (2 * previous + 2))).length =
        (Computability.encodeNat final).length := by
    rfl
  cases remaining with
  | zero =>
      simp [fuelAddChunkBodyCost, flatCountdownBodyCost,
        fuelMultiplyLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits]
      omega
  | succ remaining =>
      have nextProcessedBound :
          processed + 1 ≤ stateCount := by omega
      have nextBound : current + chunk ≤ final := by
        have multiplied :=
          Nat.mul_le_mul_right chunk nextProcessedBound
        calc
          current + chunk =
              1 + (processed + 1) * chunk := by
            dsimp [current]
            ring
          _ ≤ 1 + stateCount * chunk :=
            Nat.add_le_add_left multiplied 1
          _ = final := by rfl
      have nextBits := encodeNat_length_mono nextBound
      have chunkNextBound :
          current + (2 * previous + 2) ≤ final := by
        exact nextBound
      have chunkNextBits :=
        encodeNat_length_mono chunkNextBound
      have nextDirectBits :
          (Computability.encodeNat
            (1 + processed * (2 * previous + 2) +
              (2 * previous + 2))).length =
            (Computability.encodeNat
              (current + chunk)).length := by
        rfl
      have remainingBound : remaining ≤ stateCount := by omega
      have remainingBits :=
        encodeNat_length_mono remainingBound
      have inputRemainingBound :
          remaining + 1 ≤ stateCount := by omega
      have inputRemainingBits :=
        encodeNat_length_mono inputRemainingBound
      have chunkCost :=
        fuelAddChunkCost_le stateCount previous current
      have chunkCostDirect :
          fuelAddChunkCost
              [stateCount, previous,
                1 + processed * (2 * previous + 2)] =
            fuelAddChunkCost [stateCount, previous, current] := by
        rfl
      simp [fuelAddChunkBound, encodedListSpace_cons,
        encodedListSpace_nil] at chunkCost
      simp [fuelAddChunkBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, fuelMultiplyLoopCost,
        prependCost, idCost, headCost,
        nilCost, oneCost, zeroCost, zeroPrimeCost, tailCost,
        succCost, Code.fuelAddChunkList,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits]
      omega

theorem fuelMultiply (values : List Nat) :
    EvaluatorCodeFits
      ((Code.flatIterate Code.fuelAddChunkCode).comp
        Code.fuelMultiplyInputCode)
      values
      [values[0]?.getD 0, values[1]?.getD 0,
        1 + values[0]?.getD 0 *
          (2 * values[1]?.getD 0 + 2)]
      (fuelMultiplyCost values) where
  input_space := by
    have inputSpace := (fuelMultiplyInput values).input_space
    simp only [fuelMultiplyCost]
    omega
  output_space := by
    simp [fuelMultiplyCost, fuelMultiplyLoopCost]
    omega
  call continuation bound budget after := by
    let stateCount := values[0]?.getD 0
    let previous := values[1]?.getD 0
    have budget' :
        fuelMultiplyInputCost values +
            fuelMultiplyLoopCost values +
            continuationSpace continuation ≤
          bound := by
      simpa [fuelMultiplyCost] using budget
    have finalPayload :
        ((Code.fuelAddChunkList)^[stateCount])
            [stateCount, previous, 1] =
          [stateCount, previous,
            1 + stateCount * (2 * previous + 2)] :=
      Code.fuelAddChunkList_iterate
        stateCount stateCount previous 1
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.fuelAddChunkCode)
          continuation
          [stateCount, stateCount, previous, 1] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := fuelAddChunkBodyCost)
          (invariant :=
            FuelMultiplyInvariant stateCount previous)
      · exact fuelAddChunkBody
      · exact
          fuelMultiplyInvariant_initial stateCount previous
      · exact
          fuelMultiplyInvariant_preserved stateCount previous
      · intro remaining payload invariant
        have bodyCost :=
          fuelAddChunkBodyCost_le_multiplyLoopCost
            stateCount previous remaining payload invariant
        change
          fuelAddChunkBodyCost remaining payload ≤
            fuelMultiplyLoopCost values at bodyCost
        omega
      · rw [finalPayload]
        simpa [stateCount, previous] using after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.fuelAddChunkCode)
        continuation
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation
            [stateCount, stateCount, previous, 1]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        have loopInputSpace :
            encodedListSpace
                [stateCount, stateCount, previous, 1] ≤
              fuelMultiplyLoopCost values := by
          simp [fuelMultiplyLoopCost,
            stateCount, previous]
          omega
        omega
      · exact flatCall
    have inputCall :=
      (fuelMultiplyInput values).call
        loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp]
          omega)
        (by
          simpa [stateCount, previous] using afterInput)
    exact EvaluatorCallFits.comp inputCall

def fuelStepCost (values : List Nat) : Nat :=
  let multiplied :=
    [values[0]?.getD 0, values[1]?.getD 0,
      1 + values[0]?.getD 0 *
        (2 * values[1]?.getD 0 + 2)]
  fuelStepOutputCost multiplied + fuelMultiplyCost values

theorem fuelStep (values : List Nat) :
    EvaluatorCodeFits Code.fuelStepCode values
      (Code.fuelStepList values)
      (fuelStepCost values) := by
  have multiplied := fuelMultiply values
  have projected :=
    fuelStepOutput
      [values[0]?.getD 0, values[1]?.getD 0,
        1 + values[0]?.getD 0 *
          (2 * values[1]?.getD 0 + 2)]
  have result := comp projected multiplied
  simpa [Code.fuelStepCode, Code.fuelStepList,
    fuelStepCost] using result

def fuelStepBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.fuelStepList
    fuelStepCost remaining payload

theorem fuelStepBody
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.fuelStepCode)
      (remaining :: payload)
      (flatCountdownOutput Code.fuelStepList
        remaining payload)
      (fuelStepBodyCost remaining payload) := by
  simpa [fuelStepBodyCost] using
    flatCountdownBody fuelStep remaining payload

def divideEvalFuelInputCost (values : List Nat) : Nat :=
  let restCost :=
    prependCost values [values[0]?.getD 0] [1]
      (getCost 0 values) (oneCost values)
  prependCost values [values[1]?.getD 0]
    [values[0]?.getD 0, 1]
    (getCost 1 values) restCost

theorem divideEvalFuelInput (values : List Nat) :
    EvaluatorCodeFits Code.divideEvalFuelInputCode values
      [values[1]?.getD 0, values[0]?.getD 0, 1]
      (divideEvalFuelInputCost values) := by
  have rest := prepend (get 0 values) (one values)
  have result := prepend (get 1 values) rest
  simpa [Code.divideEvalFuelInputCode,
    divideEvalFuelInputCost, prependCost] using result

theorem divideEvalFuel_pos
    (stateCount depth : Nat) :
    0 < LeanTrominoes.FiniteState.divideEvalFuel
      stateCount depth := by
  induction depth with
  | zero =>
      simp [LeanTrominoes.FiniteState.divideEvalFuel]
  | succ depth induction =>
      simp only [LeanTrominoes.FiniteState.divideEvalFuel]
      omega

theorem divideEvalFuel_le_succ
    (stateCount depth : Nat) :
    LeanTrominoes.FiniteState.divideEvalFuel stateCount depth ≤
      LeanTrominoes.FiniteState.divideEvalFuel
        stateCount (depth + 1) := by
  cases stateCount with
  | zero =>
      induction depth with
      | zero =>
          simp [LeanTrominoes.FiniteState.divideEvalFuel]
      | succ depth induction =>
          simp [LeanTrominoes.FiniteState.divideEvalFuel]
  | succ stateCount =>
      let fuel :=
        LeanTrominoes.FiniteState.divideEvalFuel
          (stateCount + 1) depth
      have factor :
          2 * fuel + 2 ≤
            (stateCount + 1) * (2 * fuel + 2) := by
        have countPositive : 0 < stateCount + 1 := by omega
        exact Nat.le_mul_of_pos_left _ countPositive
      simp only [LeanTrominoes.FiniteState.divideEvalFuel]
      change fuel ≤ 1 + (stateCount + 1) * (2 * fuel + 2)
      omega

theorem divideEvalFuel_mono_depth
    (stateCount : Nat) {smaller larger : Nat}
    (bounded : smaller ≤ larger) :
    LeanTrominoes.FiniteState.divideEvalFuel
        stateCount smaller ≤
      LeanTrominoes.FiniteState.divideEvalFuel
        stateCount larger := by
  induction larger with
  | zero =>
      have : smaller = 0 := by omega
      simp [this]
  | succ larger induction =>
      by_cases equal : smaller = larger + 1
      · simp [equal]
      · have smallerBound : smaller ≤ larger := by omega
        exact (induction smallerBound).trans
          (divideEvalFuel_le_succ stateCount larger)

def fuelStepBound (stateCount current : Nat) : Nat :=
  let next :=
    1 + stateCount * (2 * current + 2)
  1000000000000000000000000000000000000000 *
    (encodedListSpace [stateCount, current] +
      encodedListSpace [stateCount, next] + 1)

theorem fuelStepCost_le
    (stateCount current : Nat)
    (monotone :
      current ≤ 1 + stateCount * (2 * current + 2)) :
    fuelStepCost [stateCount, current] ≤
      fuelStepBound stateCount current := by
  let next := 1 + stateCount * (2 * current + 2)
  have currentBits :=
    encodeNat_length_mono
      (show current ≤ next by simpa [next] using monotone)
  have stateCountSuccessorBits :=
    encodeNat_succ_length_le stateCount
  have stateCountPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using stateCountSuccessorBits
  have currentSuccessorBits :=
    encodeNat_succ_length_le current
  have currentPlusBits :
      (Computability.encodeNat (current + 1)).length ≤
        (Computability.encodeNat current).length + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccessorBits
  have nextSuccessorBits :=
    encodeNat_succ_length_le next
  have nextPlusBits :
      (Computability.encodeNat (next + 1)).length ≤
        (Computability.encodeNat next).length + 1 := by
    simpa [Nat.succ_eq_add_one] using nextSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have nextDirectBits :
      (Computability.encodeNat
        (1 + stateCount * (2 * current + 2))).length =
        (Computability.encodeNat next).length := by
    rfl
  have nextDirectPlusBits :
      (Computability.encodeNat
        (1 + stateCount * (2 * current + 2) + 1)).length =
        (Computability.encodeNat (next + 1)).length := by
    rfl
  simp [fuelStepCost, fuelStepBound, fuelStepOutputCost,
    fuelMultiplyCost, fuelMultiplyInputCost,
    fuelMultiplyLoopCost, prependCost, getCost, dropCost,
    idCost, headCost, nilCost, oneCost, zeroCost,
    zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits, oneBits]
  omega

def fuelOuterLoopCost (values : List Nat) : Nat :=
  let stateCount := values[0]?.getD 0
  let depth := values[1]?.getD 0
  100000000000000000000000000000000000000000000000000 *
    (3 * encodedListSpace [depth, stateCount, 1] +
      3 * encodedListSpace [stateCount, 1] +
      encodedListSpace
        [stateCount,
          LeanTrominoes.FiniteState.divideEvalFuel
            stateCount depth] + 1)

def divideEvalFuelCost (values : List Nat) : Nat :=
  divideEvalFuelInputCost values +
    fuelOuterLoopCost values +
      getCost 1
        [values[0]?.getD 0,
          LeanTrominoes.FiniteState.divideEvalFuel
            (values[0]?.getD 0) (values[1]?.getD 0)]

def FuelOuterInvariant
    (stateCount depth remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = depth ∧
      payload =
        [stateCount,
          LeanTrominoes.FiniteState.divideEvalFuel
            stateCount processed]

theorem fuelOuterInvariant_initial
    (stateCount depth : Nat) :
    FuelOuterInvariant stateCount depth depth
      [stateCount, 1] := by
  exact ⟨0, by simp, by
    simp [LeanTrominoes.FiniteState.divideEvalFuel]⟩

theorem fuelOuterInvariant_preserved
    (stateCount depth remaining : Nat)
    (payload : List Nat)
    (invariant :
      FuelOuterInvariant stateCount depth
        (remaining + 1) payload) :
    FuelOuterInvariant stateCount depth remaining
      (Code.fuelStepList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.fuelStepList,
    LeanTrominoes.FiniteState.divideEvalFuel]

theorem fuelStepBodyCost_le_outerLoopCost
    (stateCount depth remaining : Nat)
    (payload : List Nat)
    (invariant :
      FuelOuterInvariant stateCount depth remaining payload) :
    fuelStepBodyCost remaining payload ≤
      fuelOuterLoopCost [stateCount, depth] := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  let current :=
    LeanTrominoes.FiniteState.divideEvalFuel
      stateCount processed
  let final :=
    LeanTrominoes.FiniteState.divideEvalFuel
      stateCount depth
  have processedBound : processed ≤ depth := by omega
  have currentBound : current ≤ final :=
    divideEvalFuel_mono_depth stateCount processedBound
  have currentBits := encodeNat_length_mono currentBound
  have stateCountSuccessorBits :=
    encodeNat_succ_length_le stateCount
  have stateCountPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using stateCountSuccessorBits
  have currentSuccessorBits :=
    encodeNat_succ_length_le current
  have currentPlusBits :
      (Computability.encodeNat (current + 1)).length ≤
        (Computability.encodeNat current).length + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have currentDirectBits :
      (Computability.encodeNat
        (LeanTrominoes.FiniteState.divideEvalFuel
          stateCount processed)).length =
        (Computability.encodeNat current).length := by
    rfl
  have finalDirectBits :
      (Computability.encodeNat
        (LeanTrominoes.FiniteState.divideEvalFuel
          stateCount depth)).length =
        (Computability.encodeNat final).length := by
    rfl
  cases remaining with
  | zero =>
      simp [fuelStepBodyCost, flatCountdownBodyCost,
        fuelOuterLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits]
      omega
  | succ remaining =>
      have nextProcessedBound :
          processed + 1 ≤ depth := by omega
      have nextBound :
          LeanTrominoes.FiniteState.divideEvalFuel
              stateCount (processed + 1) ≤
            final :=
        divideEvalFuel_mono_depth
          stateCount nextProcessedBound
      have nextBits := encodeNat_length_mono nextBound
      have remainingBound : remaining ≤ depth := by omega
      have remainingBits :=
        encodeNat_length_mono remainingBound
      have inputRemainingBound :
          remaining + 1 ≤ depth := by omega
      have inputRemainingBits :=
        encodeNat_length_mono inputRemainingBound
      have currentNext :=
        divideEvalFuel_le_succ stateCount processed
      have stepCost :=
        fuelStepCost_le stateCount current
          (by
            simpa [current,
              LeanTrominoes.FiniteState.divideEvalFuel] using
              currentNext)
      have nextDirectBits :
          (Computability.encodeNat
            (1 + stateCount *
              (2 *
                LeanTrominoes.FiniteState.divideEvalFuel
                  stateCount processed + 2))).length ≤
            (Computability.encodeNat final).length := by
        simpa [LeanTrominoes.FiniteState.divideEvalFuel] using
          nextBits
      have nextCurrentBits :
          (Computability.encodeNat
            (1 + stateCount * (2 * current + 2))).length =
            (Computability.encodeNat
              (1 + stateCount *
                (2 *
                  LeanTrominoes.FiniteState.divideEvalFuel
                    stateCount processed + 2))).length := by
        rfl
      have stepCostDirect :
          fuelStepCost
              [stateCount,
                LeanTrominoes.FiniteState.divideEvalFuel
                  stateCount processed] =
            fuelStepCost [stateCount, current] := by
        rfl
      simp [fuelStepBound, encodedListSpace_cons,
        encodedListSpace_nil] at stepCost
      simp [fuelStepBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, fuelOuterLoopCost,
        prependCost, idCost, headCost, nilCost, oneCost,
        zeroCost, zeroPrimeCost, tailCost, succCost,
        Code.fuelStepList, encodedListSpace_cons,
        encodedListSpace_nil, zeroBits, oneBits]
      omega

theorem divideEvalFuel (values : List Nat) :
    EvaluatorCodeFits Code.divideEvalFuelCode values
      [LeanTrominoes.FiniteState.divideEvalFuel
        (values[0]?.getD 0) (values[1]?.getD 0)]
      (divideEvalFuelCost values) where
  input_space := by
    have inputSpace := (divideEvalFuelInput values).input_space
    simp only [divideEvalFuelCost]
    omega
  output_space := by
    let stateCount := values[0]?.getD 0
    let depth := values[1]?.getD 0
    let fuel :=
      LeanTrominoes.FiniteState.divideEvalFuel
        stateCount depth
    have outputSpace :=
      (get 1 [stateCount, fuel]).output_space
    have outputSpace' :
        encodedListSpace [fuel] ≤
          getCost 1 [stateCount, fuel] := by
      simpa using outputSpace
    simp only [divideEvalFuelCost]
    change
      encodedListSpace [fuel] ≤
        divideEvalFuelInputCost values +
          fuelOuterLoopCost values +
            getCost 1 [stateCount, fuel]
    omega
  call continuation bound budget after := by
    let stateCount := values[0]?.getD 0
    let depth := values[1]?.getD 0
    let fuel :=
      LeanTrominoes.FiniteState.divideEvalFuel
        stateCount depth
    have budget' :
        divideEvalFuelInputCost values +
            fuelOuterLoopCost values +
            getCost 1 [stateCount, fuel] +
            continuationSpace continuation ≤
          bound := by
      simpa [divideEvalFuelCost,
        stateCount, depth, fuel] using budget
    have getCall :
        EvaluatorCallFits (Code.get 1) continuation
          [stateCount, fuel] bound :=
      (get 1 [stateCount, fuel]).call
        continuation bound (by omega)
        (by simpa [stateCount, depth, fuel] using after)
    let getContinuation :=
      ToPartrec.Cont.comp (Code.get 1) continuation
    have afterLoop :
        EvaluatorExecutionFits bound
          (.ret getContinuation [stateCount, fuel]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        have finalSpace :
            encodedListSpace [stateCount, fuel] ≤
              fuelOuterLoopCost values := by
          simp [fuelOuterLoopCost,
            stateCount, depth, fuel]
          omega
        omega
      · exact getCall
    have finalPayload :
        ((Code.fuelStepList)^[depth])
            [stateCount, 1] =
          [stateCount, fuel] := by
      simpa [fuel] using
        Code.fuelStepList_iterate stateCount depth
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.fuelStepCode)
          getContinuation
          [depth, stateCount, 1] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := fuelStepBodyCost)
          (invariant :=
            FuelOuterInvariant stateCount depth)
      · exact fuelStepBody
      · exact fuelOuterInvariant_initial stateCount depth
      · exact fuelOuterInvariant_preserved stateCount depth
      · intro remaining payload invariant
        have bodyCost :=
          fuelStepBodyCost_le_outerLoopCost
            stateCount depth remaining payload invariant
        change
          fuelStepBodyCost remaining payload ≤
            fuelOuterLoopCost values at bodyCost
        simp only [getContinuation,
          continuationSpace_comp]
        omega
      · rw [finalPayload]
        exact afterLoop
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.fuelStepCode)
        getContinuation
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [depth, stateCount, 1]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [getContinuation,
          continuationSpace_comp]
        have loopInputSpace :
            encodedListSpace [depth, stateCount, 1] ≤
              fuelOuterLoopCost values := by
          simp [fuelOuterLoopCost,
            stateCount, depth]
          omega
        omega
      · exact flatCall
    have inputCall :=
      (divideEvalFuelInput values).call
        loopContinuation bound
        (by
          simp only [loopContinuation, getContinuation,
            continuationSpace_comp]
          omega)
        (by
          simpa [stateCount, depth] using afterInput)
    have loopWithInput :=
      EvaluatorCallFits.comp inputCall
    have whole :=
      EvaluatorCallFits.comp loopWithInput
    simpa [Code.divideEvalFuelCode,
      loopContinuation, getContinuation] using whole

end EvaluatorCodeFits

end PartrecToTM2
end Turing
