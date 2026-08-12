import LeanTrominoes.PartrecPackedAssignmentAt
import LeanTrominoes.PartrecPackedAssignmentLookupSpace

/-!
# Evaluator-space certificate for five-column packed lookup

The number of frontier columns is the fixed constant five.  This module fits
one numbered stage compositionally and then unrolls five copies.  Every scan
reuses the uniform one-column workspace certificate; the repeated field
projections affect only the constant factor.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedAssignmentLookupColumnEqArgumentsCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  prependCost state [queriedColumn] [currentColumn]
    (getCost 1 state) (numeralCost currentColumn state)

theorem packedAssignmentLookupColumnEqArguments
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnEqArgumentsCode
        currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [queriedColumn, currentColumn]
      (packedAssignmentLookupColumnEqArgumentsCost
        currentColumn motif queriedColumn target accumulator) := by
  simpa [Code.packedAssignmentLookupColumnEqArgumentsCode,
    packedAssignmentLookupColumnEqArgumentsCost,
    prependCost, Code.packedAssignmentLookupState] using
    prepend
      (get 1
        (Code.packedAssignmentLookupState motif queriedColumn
          target accumulator))
      (numeral currentColumn
        (Code.packedAssignmentLookupState motif queriedColumn
          target accumulator))

def packedAssignmentLookupColumnSelectedCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  natEqCost queriedColumn currentColumn +
    packedAssignmentLookupColumnEqArgumentsCost
      currentColumn motif queriedColumn target accumulator

theorem packedAssignmentLookupColumnSelected
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnSelectedCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [(decide (queriedColumn = currentColumn)).toNat]
      (packedAssignmentLookupColumnSelectedCost
        currentColumn motif queriedColumn target accumulator) := by
  have selected :=
    comp (natEq queriedColumn currentColumn)
      (packedAssignmentLookupColumnEqArguments
        currentColumn motif queriedColumn target accumulator)
  by_cases equal : queriedColumn = currentColumn
  · subst queriedColumn
    simpa [Code.packedAssignmentLookupColumnSelectedCode,
      packedAssignmentLookupColumnSelectedCost] using selected
  · simpa [Code.packedAssignmentLookupColumnSelectedCode,
      packedAssignmentLookupColumnSelectedCost, equal] using selected

def packedAssignmentLookupColumnInputCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  let selected :=
    (decide (queriedColumn = currentColumn)).toNat
  let rest5 :=
    prependCost state [accumulator.2.2.toNat] [selected]
      (getCost 5 state)
      (packedAssignmentLookupColumnSelectedCost
        currentColumn motif queriedColumn target accumulator)
  let rest4 :=
    prependCost state [accumulator.2.1]
      [accumulator.2.2.toNat, selected]
      (getCost 4 state) rest5
  let rest3 :=
    prependCost state [accumulator.1]
      [accumulator.2.1, accumulator.2.2.toNat, selected]
      (getCost 3 state) rest4
  let rest2 :=
    prependCost state [Encodable.encode target]
      [accumulator.1, accumulator.2.1,
        accumulator.2.2.toNat, selected]
      (getCost 2 state) rest3
  prependCost state [Encodable.encode motif]
    [Encodable.encode target, accumulator.1,
      accumulator.2.1, accumulator.2.2.toNat, selected]
    (getCost 0 state) rest2

theorem packedAssignmentLookupColumnInput
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnInputCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [Encodable.encode motif, Encodable.encode target,
        accumulator.1, accumulator.2.1,
        accumulator.2.2.toNat,
        (decide (queriedColumn = currentColumn)).toNat]
      (packedAssignmentLookupColumnInputCost
        currentColumn motif queriedColumn target accumulator) := by
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  have rest5 :=
    prepend (get 5 state)
      (packedAssignmentLookupColumnSelected currentColumn motif
        queriedColumn target accumulator)
  have rest4 := prepend (get 4 state) rest5
  have rest3 := prepend (get 3 state) rest4
  have rest2 := prepend (get 2 state) rest3
  have result := prepend (get 0 state) rest2
  simpa [Code.packedAssignmentLookupColumnInputCode,
    packedAssignmentLookupColumnInputCost,
    Code.packedAssignmentLookupState, prependCost,
    state] using result

def packedAssignmentLookupColumnCallCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let selected := decide (queriedColumn = currentColumn)
  packedLookupColumnCodeCost motif target
      accumulator.1 accumulator.2.1 accumulator.2.2 selected +
    packedAssignmentLookupColumnInputCost currentColumn motif
      queriedColumn target accumulator

theorem packedAssignmentLookupColumnCall
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnCallCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      (Code.packedLookupColumnResult motif target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide (queriedColumn = currentColumn)))
      (packedAssignmentLookupColumnCallCost
        currentColumn motif queriedColumn target accumulator) := by
  simpa [Code.packedAssignmentLookupColumnCallCode,
    packedAssignmentLookupColumnCallCost] using
    comp
      (packedLookupColumn motif target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide (queriedColumn = currentColumn)))
      (packedAssignmentLookupColumnInput currentColumn motif
        queriedColumn target accumulator)

def packedAssignmentLookupColumnResultFieldCost
    (currentColumn outputField : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let result :=
    Code.packedLookupColumnResult motif target
      accumulator.1 accumulator.2.1 accumulator.2.2
      (decide (queriedColumn = currentColumn))
  getCost outputField result +
    packedAssignmentLookupColumnCallCost currentColumn motif
      queriedColumn target accumulator

theorem packedAssignmentLookupColumnResultField
    (currentColumn outputField : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnResultFieldCode
        currentColumn outputField)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [(Code.packedLookupColumnResult motif target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide
          (queriedColumn = currentColumn)))[outputField]?.getD 0]
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn outputField motif queriedColumn
        target accumulator) := by
  let result :=
    Code.packedLookupColumnResult motif target
      accumulator.1 accumulator.2.1 accumulator.2.2
      (decide (queriedColumn = currentColumn))
  simpa [Code.packedAssignmentLookupColumnResultFieldCode,
    packedAssignmentLookupColumnResultFieldCost, result] using
    comp (get outputField result)
      (packedAssignmentLookupColumnCall currentColumn motif
        queriedColumn target accumulator)

def packedAssignmentLookupColumnStageCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  let next :=
    Code.packedAssignmentLookupApplyColumn currentColumn motif
      queriedColumn target accumulator
  let rest6 :=
    prependCost state [next.2.1] [next.2.2.toNat]
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn 3 motif queriedColumn target accumulator)
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn 4 motif queriedColumn target accumulator)
  let rest5 :=
    prependCost state [next.1]
      [next.2.1, next.2.2.toNat]
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn 2 motif queriedColumn target accumulator)
      rest6
  let rest3 :=
    prependCost state [Encodable.encode target]
      [next.1, next.2.1, next.2.2.toNat]
      (getCost 2 state) rest5
  let rest2 :=
    prependCost state [queriedColumn]
      [Encodable.encode target, next.1,
        next.2.1, next.2.2.toNat]
      (getCost 1 state) rest3
  prependCost state [Encodable.encode motif]
    [queriedColumn, Encodable.encode target,
      next.1, next.2.1, next.2.2.toNat]
    (getCost 0 state) rest2

theorem packedAssignmentLookupColumnStage
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnStageCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      (Code.packedAssignmentLookupState motif queriedColumn target
        (Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator))
      (packedAssignmentLookupColumnStageCost
        currentColumn motif queriedColumn target accumulator) := by
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  have rest6 :=
    prepend
      (packedAssignmentLookupColumnResultField currentColumn 3 motif
        queriedColumn target accumulator)
      (packedAssignmentLookupColumnResultField currentColumn 4 motif
        queriedColumn target accumulator)
  have rest5 :=
    prepend
      (packedAssignmentLookupColumnResultField currentColumn 2 motif
        queriedColumn target accumulator)
      rest6
  have rest3 := prepend (get 2 state) rest5
  have rest2 := prepend (get 1 state) rest3
  have result := prepend (get 0 state) rest2
  simpa [Code.packedAssignmentLookupColumnStageCode,
    packedAssignmentLookupColumnStageCost,
    Code.packedAssignmentLookupState,
    Code.packedAssignmentLookupApplyColumn,
    Code.packedLookupColumnResult_eq_outcome,
    prependCost, state] using result

set_option maxHeartbeats 1600000 in
theorem packedAssignmentLookupColumnStageCost_le_linear
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool)
    (initialWord digitLimit : Nat)
    (columnBound : currentColumn < 5)
    (wordBound : accumulator.1 ≤ initialWord)
    (digitBound : accumulator.2.1 ≤ digitLimit) :
    packedAssignmentLookupColumnStageCost currentColumn motif
        queriedColumn target accumulator ≤
      100000000000000000000 *
        (encodedListSpace
          [32 * (Encodable.encode motif +
            Encodable.encode motif + Encodable.encode motif +
            Encodable.encode target + queriedColumn +
            initialWord + digitLimit + 32) + 200] + 1) := by
  let motifCode := Encodable.encode motif
  let targetCode := Encodable.encode target
  let selected := decide (queriedColumn = currentColumn)
  let next :=
    Code.packedAssignmentLookupApplyColumn currentColumn motif
      queriedColumn target accumulator
  let localScannerLimit :=
    16 * (motifCode + motifCode + motifCode +
      targetCode + accumulator.1 + accumulator.2.1 + 8) + 100
  let limit :=
    32 * (motifCode + motifCode + motifCode +
      targetCode + queriedColumn + initialWord +
      digitLimit + 32) + 200
  change
    packedAssignmentLookupColumnStageCost currentColumn motif
        queriedColumn target accumulator ≤
      100000000000000000000 *
        (encodedListSpace [limit] + 1)
  have nextWord :
      next.1 ≤ accumulator.1 := by
    simpa [next, selected,
      Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_word_le
        target selected motif accumulator.1 accumulator.2.1
        accumulator.2.2
  have nextDigit :
      next.2.1 ≤ accumulator.2.1 + 8 := by
    simpa [next, selected,
      Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_digit_le
        target selected motif accumulator.1 accumulator.2.1
        accumulator.2.2
  have scannerLimit : localScannerLimit ≤ limit := by
    simp only [localScannerLimit, limit]
    omega
  have scannerLimitBits :=
    encodeNat_length_mono scannerLimit
  have scanner :=
    packedLookupColumnCodeCost_le_linear motif target
      accumulator.1 accumulator.2.1 accumulator.2.2 selected
  have scannerLocal :
      packedLookupColumnCodeCost motif target
          accumulator.1 accumulator.2.1
          accumulator.2.2 selected ≤
        1000000000000000000 *
          (encodedListSpace [localScannerLimit] + 1) := by
    simpa [localScannerLimit, motifCode, targetCode] using scanner
  have scannerGlobal :
      packedLookupColumnCodeCost motif target
          accumulator.1 accumulator.2.1
          accumulator.2.2 selected ≤
        1000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at scannerLocal
    simp only [encodedListSpace_cons,
      encodedListSpace_nil]
    omega
  have equality :=
    natEqCost_le_linear queriedColumn currentColumn
  have equalityLimit :
      2 * (queriedColumn + currentColumn) + 4 ≤ limit := by
    simp only [limit]
    omega
  have equalityLimitBits :=
    encodeNat_length_mono equalityLimit
  have equalityGlobal :
      natEqCost queriedColumn currentColumn ≤
        10000000000 *
          (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at equality ⊢
    omega
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have targetBound : targetCode ≤ limit := by
    simp only [limit]
    omega
  have queryBound : queriedColumn ≤ limit := by
    simp only [limit]
    omega
  have currentBound : currentColumn ≤ limit := by
    simp only [limit]
    omega
  have wordLimit : accumulator.1 ≤ limit :=
    wordBound.trans (by
      simp only [limit]
      omega)
  have digitLimit' : accumulator.2.1 ≤ limit :=
    digitBound.trans (by
      simp only [limit]
      omega)
  have nextWordLimit : next.1 ≤ limit :=
    nextWord.trans wordLimit
  have nextDigitLimit : next.2.1 ≤ limit := by
    simp only [limit]
    omega
  have motifBits := encodeNat_length_mono motifBound
  have targetBits := encodeNat_length_mono targetBound
  have queryBits := encodeNat_length_mono queryBound
  have currentBits := encodeNat_length_mono currentBound
  have wordBits := encodeNat_length_mono wordLimit
  have digitBits := encodeNat_length_mono digitLimit'
  have nextWordBits := encodeNat_length_mono nextWordLimit
  have nextDigitBits := encodeNat_length_mono nextDigitLimit
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have targetSuccBits :=
    encodeNat_length_mono
      (show targetCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have querySuccBits :=
    encodeNat_length_mono
      (show queriedColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show accumulator.1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have digitSuccBits :=
    encodeNat_length_mono
      (show accumulator.2.1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have nextWordSuccBits :=
    encodeNat_length_mono
      (show next.1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have nextDigitSuccBits :=
    encodeNat_length_mono
      (show next.2.1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode motif)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifBits
  have targetBitsRaw :
      (Computability.encodeNat
        (Encodable.encode target)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [targetCode] using targetBits
  have motifSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode motif + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifSuccBits
  have targetSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode target + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [targetCode] using targetSuccBits
  have nextWordBitsRaw :
      (Computability.encodeNat
        (Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator).1).length ≤
        (Computability.encodeNat limit).length := by
    simpa [next] using nextWordBits
  have nextDigitBitsRaw :
      (Computability.encodeNat
        (Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator).2.1).length ≤
        (Computability.encodeNat limit).length := by
    simpa [next] using nextDigitBits
  have nextWordSuccBitsRaw :
      (Computability.encodeNat
        ((Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator).1 + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [next] using nextWordSuccBits
  have nextDigitSuccBitsRaw :
      (Computability.encodeNat
        ((Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator).2.1 + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [next] using nextDigitSuccBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have threeBits :
      (Computability.encodeNat 3).length = 2 := rfl
  have fourBits :
      (Computability.encodeNat 4).length = 3 := rfl
  have threeLimitBits :
      (Computability.encodeNat 3).length ≤
        (Computability.encodeNat limit).length :=
    encodeNat_length_mono (by
      simp only [limit]
      omega)
  have fourLimitBits :
      (Computability.encodeNat 4).length ≤
        (Computability.encodeNat limit).length :=
    encodeNat_length_mono (by
      simp only [limit]
      omega)
  have eqArgumentsGlobal :
      packedAssignmentLookupColumnEqArgumentsCost currentColumn
          motif queriedColumn target accumulator ≤
        10000000000000 *
          (encodedListSpace [limit] + 1) := by
    interval_cases currentColumn <;>
      cases accumulatorFound : accumulator.2.2 <;>
      simp [packedAssignmentLookupColumnEqArgumentsCost,
        Code.packedAssignmentLookupState,
        prependCost, getCost, dropCost, headCost,
        idCost, nilCost, tailCost, zeroPrimeCost,
        succCost, zeroCost, numeralCost, addConstCost,
        encodedListSpace_cons, encodedListSpace_nil,
        accumulatorFound,
        zeroBits, oneBits, twoBits, threeBits, fourBits] <;>
      omega
  have selectedGlobal :
      packedAssignmentLookupColumnSelectedCost currentColumn
          motif queriedColumn target accumulator ≤
        100000000000000 *
          (encodedListSpace [limit] + 1) := by
    simp only [packedAssignmentLookupColumnSelectedCost]
    omega
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at scannerGlobal equalityGlobal eqArgumentsGlobal selectedGlobal
  have scannerGlobalActual :
      packedLookupColumnCodeCost motif target
          accumulator.1 accumulator.2.1 accumulator.2.2
          (decide (queriedColumn = currentColumn)) ≤
        1000000000000000000 *
          ((Computability.encodeNat limit).length + 1 + 0 + 1) := by
    simpa [selected] using scannerGlobal
  have inputGlobal :
      packedAssignmentLookupColumnInputCost currentColumn
          motif queriedColumn target accumulator ≤
        10000000000000000 *
          (encodedListSpace [limit] + 1) := by
    cases accumulatorFound : accumulator.2.2 <;>
      cases selectedTag : selected <;>
      simp [packedAssignmentLookupColumnInputCost,
        Code.packedAssignmentLookupState,
        prependCost, getCost, dropCost, headCost,
        idCost, nilCost, tailCost, zeroPrimeCost,
        succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        selected, selectedTag,
        accumulatorFound,
        zeroBits, oneBits, twoBits] <;>
      omega
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at inputGlobal
  have callGlobal :
      packedAssignmentLookupColumnCallCost currentColumn
          motif queriedColumn target accumulator ≤
        2000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    have sumBound :
        packedLookupColumnCodeCost motif target accumulator.1
            accumulator.2.1 accumulator.2.2
            (decide (queriedColumn = currentColumn)) +
          packedAssignmentLookupColumnInputCost currentColumn motif
            queriedColumn target accumulator ≤
          2000000000000000000 *
            ((Computability.encodeNat limit).length + 1 + 0 + 1) := by
      omega
    simpa only [packedAssignmentLookupColumnCallCost,
      encodedListSpace_cons, encodedListSpace_nil] using sumBound
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at callGlobal
  have resultEq :
      Code.packedLookupColumnResult motif target
          accumulator.1 accumulator.2.1 accumulator.2.2
          (decide (queriedColumn = currentColumn)) =
        [motifCode, targetCode, next.1,
          next.2.1, next.2.2.toNat] := by
    simp [Code.packedLookupColumnResult_eq_outcome,
      next, motifCode, targetCode,
      Code.packedAssignmentLookupApplyColumn]
  have wordFieldGlobal :
      packedAssignmentLookupColumnResultFieldCost currentColumn 2
          motif queriedColumn target accumulator ≤
        3000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simp only [packedAssignmentLookupColumnResultFieldCost]
    rw [resultEq]
    cases nextFound : next.2.2 <;>
      simp [getCost, dropCost, headCost,
        idCost, nilCost, tailCost, zeroPrimeCost,
        succCost, encodedListSpace_cons,
        encodedListSpace_nil, motifCode, targetCode,
        zeroBits, oneBits] <;>
      omega
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at wordFieldGlobal
  have digitFieldGlobal :
      packedAssignmentLookupColumnResultFieldCost currentColumn 3
          motif queriedColumn target accumulator ≤
        3000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simp only [packedAssignmentLookupColumnResultFieldCost]
    rw [resultEq]
    cases nextFound : next.2.2 <;>
      simp [getCost, dropCost, headCost,
        idCost, nilCost, tailCost, zeroPrimeCost,
        succCost, encodedListSpace_cons,
        encodedListSpace_nil, motifCode, targetCode,
        zeroBits, oneBits] <;>
      omega
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at digitFieldGlobal
  have foundFieldGlobal :
      packedAssignmentLookupColumnResultFieldCost currentColumn 4
          motif queriedColumn target accumulator ≤
        3000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simp only [packedAssignmentLookupColumnResultFieldCost]
    rw [resultEq]
    cases nextFound : next.2.2 <;>
      simp [getCost, dropCost, headCost,
        idCost, nilCost, tailCost, zeroPrimeCost,
        succCost, encodedListSpace_cons,
        encodedListSpace_nil, motifCode, targetCode,
        zeroBits, oneBits, twoBits] <;>
      omega
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at foundFieldGlobal
  cases accumulatorFound : accumulator.2.2 <;>
    cases nextFound : next.2.2 <;>
    simp [packedAssignmentLookupColumnStageCost,
      Code.packedAssignmentLookupState,
      prependCost, getCost, dropCost, headCost,
      idCost, nilCost, tailCost, zeroPrimeCost,
      succCost, encodedListSpace_cons,
      encodedListSpace_nil,
      next, accumulatorFound, nextFound,
      zeroBits, oneBits] <;>
    omega

def packedAssignmentLookupStagesCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    Code.packedAssignmentLookupApplyColumn 0 motif queriedColumn
      target initial
  let second :=
    Code.packedAssignmentLookupApplyColumn 1 motif queriedColumn
      target first
  let third :=
    Code.packedAssignmentLookupApplyColumn 2 motif queriedColumn
      target second
  let fourth :=
    Code.packedAssignmentLookupApplyColumn 3 motif queriedColumn
      target third
  packedAssignmentLookupColumnStageCost 4 motif queriedColumn
      target fourth +
    (packedAssignmentLookupColumnStageCost 3 motif queriedColumn
        target third +
      (packedAssignmentLookupColumnStageCost 2 motif queriedColumn
          target second +
        (packedAssignmentLookupColumnStageCost 1 motif queriedColumn
            target first +
          packedAssignmentLookupColumnStageCost 0 motif queriedColumn
            target initial)))

set_option maxHeartbeats 800000 in
theorem packedAssignmentLookupStagesCost_le_linear
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupStagesCost motif queriedColumn target word ≤
      500000000000000000000 *
        (encodedListSpace
          [32 * (Encodable.encode motif +
            Encodable.encode motif + Encodable.encode motif +
            Encodable.encode target + queriedColumn +
            word + 40 + 32) + 200] + 1) := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    Code.packedAssignmentLookupApplyColumn 0 motif queriedColumn
      target initial
  let second :=
    Code.packedAssignmentLookupApplyColumn 1 motif queriedColumn
      target first
  let third :=
    Code.packedAssignmentLookupApplyColumn 2 motif queriedColumn
      target second
  let fourth :=
    Code.packedAssignmentLookupApplyColumn 3 motif queriedColumn
      target third
  let limit :=
    32 * (Encodable.encode motif +
      Encodable.encode motif + Encodable.encode motif +
      Encodable.encode target + queriedColumn +
      word + 40 + 32) + 200
  change
    packedAssignmentLookupStagesCost motif queriedColumn target word ≤
      500000000000000000000 *
        (encodedListSpace [limit] + 1)
  have firstWord : first.1 ≤ word := by
    simpa [first, initial,
      Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_word_le target
        (decide (queriedColumn = 0)) motif word 0 false
  have firstDigit : first.2.1 ≤ 8 := by
    simpa [first, initial,
      Code.packedAssignmentLookupApplyColumn] using
      Code.packedLookupColumnOutcome_digit_le target
        (decide (queriedColumn = 0)) motif word 0 false
  have secondWord : second.1 ≤ word := by
    have step :=
      Code.packedLookupColumnOutcome_word_le target
        (decide (queriedColumn = 1)) motif first.1
        first.2.1 first.2.2
    have applied : second.1 ≤ first.1 := by
      simpa [second,
        Code.packedAssignmentLookupApplyColumn] using step
    exact applied.trans firstWord
  have secondDigit : second.2.1 ≤ 16 := by
    have step :=
      Code.packedLookupColumnOutcome_digit_le target
        (decide (queriedColumn = 1)) motif first.1
        first.2.1 first.2.2
    have applied : second.2.1 ≤ first.2.1 + 8 := by
      simpa [second,
        Code.packedAssignmentLookupApplyColumn] using step
    omega
  have thirdWord : third.1 ≤ word := by
    have step :=
      Code.packedLookupColumnOutcome_word_le target
        (decide (queriedColumn = 2)) motif second.1
        second.2.1 second.2.2
    have applied : third.1 ≤ second.1 := by
      simpa [third,
        Code.packedAssignmentLookupApplyColumn] using step
    exact applied.trans secondWord
  have thirdDigit : third.2.1 ≤ 24 := by
    have step :=
      Code.packedLookupColumnOutcome_digit_le target
        (decide (queriedColumn = 2)) motif second.1
        second.2.1 second.2.2
    have applied : third.2.1 ≤ second.2.1 + 8 := by
      simpa [third,
        Code.packedAssignmentLookupApplyColumn] using step
    omega
  have fourthWord : fourth.1 ≤ word := by
    have step :=
      Code.packedLookupColumnOutcome_word_le target
        (decide (queriedColumn = 3)) motif third.1
        third.2.1 third.2.2
    have applied : fourth.1 ≤ third.1 := by
      simpa [fourth,
        Code.packedAssignmentLookupApplyColumn] using step
    exact applied.trans thirdWord
  have fourthDigit : fourth.2.1 ≤ 32 := by
    have step :=
      Code.packedLookupColumnOutcome_digit_le target
        (decide (queriedColumn = 3)) motif third.1
        third.2.1 third.2.2
    have applied : fourth.2.1 ≤ third.2.1 + 8 := by
      simpa [fourth,
        Code.packedAssignmentLookupApplyColumn] using step
    omega
  have stage0 :
      packedAssignmentLookupColumnStageCost 0 motif queriedColumn
          target initial ≤
        100000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [limit] using
      packedAssignmentLookupColumnStageCost_le_linear
        0 motif queriedColumn target initial word 40
        (by omega) (by simp [initial]) (by simp [initial])
  have stage1 :
      packedAssignmentLookupColumnStageCost 1 motif queriedColumn
          target first ≤
        100000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [limit] using
      packedAssignmentLookupColumnStageCost_le_linear
        1 motif queriedColumn target first word 40
        (by omega) firstWord (by omega)
  have stage2 :
      packedAssignmentLookupColumnStageCost 2 motif queriedColumn
          target second ≤
        100000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [limit] using
      packedAssignmentLookupColumnStageCost_le_linear
        2 motif queriedColumn target second word 40
        (by omega) secondWord (by omega)
  have stage3 :
      packedAssignmentLookupColumnStageCost 3 motif queriedColumn
          target third ≤
        100000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [limit] using
      packedAssignmentLookupColumnStageCost_le_linear
        3 motif queriedColumn target third word 40
        (by omega) thirdWord (by omega)
  have stage4 :
      packedAssignmentLookupColumnStageCost 4 motif queriedColumn
          target fourth ≤
        100000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [limit] using
      packedAssignmentLookupColumnStageCost_le_linear
        4 motif queriedColumn target fourth word 40
        (by omega) fourthWord (by omega)
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at stage0 stage1 stage2 stage3 stage4
  have sumBound :
      packedAssignmentLookupColumnStageCost 4 motif queriedColumn
          target fourth +
        (packedAssignmentLookupColumnStageCost 3 motif queriedColumn
            target third +
          (packedAssignmentLookupColumnStageCost 2 motif queriedColumn
              target second +
            (packedAssignmentLookupColumnStageCost 1 motif queriedColumn
                target first +
              packedAssignmentLookupColumnStageCost 0 motif queriedColumn
                target initial))) ≤
        500000000000000000000 *
          ((Computability.encodeNat limit).length + 1 + 0 + 1) := by
    omega
  simpa only [packedAssignmentLookupStagesCost,
    initial, first, second, third, fourth,
    encodedListSpace_cons, encodedListSpace_nil] using sumBound

theorem packedAssignmentLookupStages
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupStagesCode
      (Code.packedAssignmentLookupState motif queriedColumn target
        (word, 0, false))
      (Code.packedAssignmentLookupState motif queriedColumn target
        (Code.packedAssignmentLookupOutcome motif queriedColumn
          target word))
      (packedAssignmentLookupStagesCost motif queriedColumn
        target word) := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    Code.packedAssignmentLookupApplyColumn 0 motif queriedColumn
      target initial
  let second :=
    Code.packedAssignmentLookupApplyColumn 1 motif queriedColumn
      target first
  let third :=
    Code.packedAssignmentLookupApplyColumn 2 motif queriedColumn
      target second
  let fourth :=
    Code.packedAssignmentLookupApplyColumn 3 motif queriedColumn
      target third
  have firstTwo :=
    comp
      (packedAssignmentLookupColumnStage 1 motif queriedColumn
        target first)
      (packedAssignmentLookupColumnStage 0 motif queriedColumn
        target initial)
  have firstThree :=
    comp
      (packedAssignmentLookupColumnStage 2 motif queriedColumn
        target second)
      firstTwo
  have firstFour :=
    comp
      (packedAssignmentLookupColumnStage 3 motif queriedColumn
        target third)
      firstThree
  have allFive :=
    comp
      (packedAssignmentLookupColumnStage 4 motif queriedColumn
        target fourth)
      firstFour
  simpa [Code.packedAssignmentLookupStagesCode,
    packedAssignmentLookupStagesCost,
    Code.packedAssignmentLookupOutcome,
    initial, first, second, third, fourth] using allFive

def packedAssignmentLookupInputCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  let rest6 :=
    prependCost values [0] [0]
      (zeroCost values) (zeroCost values)
  let rest5 :=
    prependCost values [word] [0, 0]
      (getCost 3 values) rest6
  let rest3 :=
    prependCost values [Encodable.encode target]
      [word, 0, 0]
      (getCost 2 values) rest5
  let rest2 :=
    prependCost values [queriedColumn]
      [Encodable.encode target, word, 0, 0]
      (getCost 1 values) rest3
  prependCost values [Encodable.encode motif]
    [queriedColumn, Encodable.encode target, word, 0, 0]
    (getCost 0 values) rest2

theorem packedAssignmentLookupInput
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupInputCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      (Code.packedAssignmentLookupState motif queriedColumn target
        (word, 0, false))
      (packedAssignmentLookupInputCost motif queriedColumn
        target word) := by
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  have rest6 := prepend (zero values) (zero values)
  have rest5 := prepend (get 3 values) rest6
  have rest3 := prepend (get 2 values) rest5
  have rest2 := prepend (get 1 values) rest3
  have result := prepend (get 0 values) rest2
  simpa [Code.packedAssignmentLookupInputCode,
    packedAssignmentLookupInputCost,
    Code.packedAssignmentLookupState,
    prependCost, values] using result

set_option maxHeartbeats 800000 in
theorem packedAssignmentLookupInputCost_le_linear
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupInputCost motif queriedColumn target word ≤
      100000000000000000000 *
        (encodedListSpace
          [32 * (Encodable.encode motif +
            Encodable.encode motif + Encodable.encode motif +
            Encodable.encode target + queriedColumn +
            word + 40 + 32) + 200] + 1) := by
  let motifCode := Encodable.encode motif
  let targetCode := Encodable.encode target
  let limit :=
    32 * (motifCode + motifCode + motifCode +
      targetCode + queriedColumn + word + 40 + 32) + 200
  change
    packedAssignmentLookupInputCost motif queriedColumn target word ≤
      100000000000000000000 *
        (encodedListSpace [limit] + 1)
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have targetBound : targetCode ≤ limit := by
    simp only [limit]
    omega
  have queryBound : queriedColumn ≤ limit := by
    simp only [limit]
    omega
  have wordBound : word ≤ limit := by
    simp only [limit]
    omega
  have motifBits := encodeNat_length_mono motifBound
  have targetBits := encodeNat_length_mono targetBound
  have queryBits := encodeNat_length_mono queryBound
  have wordBits := encodeNat_length_mono wordBound
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have targetSuccBits :=
    encodeNat_length_mono
      (show targetCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have querySuccBits :=
    encodeNat_length_mono
      (show queriedColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show word + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedAssignmentLookupInputCost,
    prependCost, getCost, dropCost, headCost,
    idCost, nilCost, tailCost, zeroPrimeCost,
    succCost, zeroCost,
    encodedListSpace_cons, encodedListSpace_nil,
    motifCode, targetCode, zeroBits] at *;
    omega

def packedAssignmentLookupProjectionCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (outcome : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn target outcome
  prependCost state [outcome.2.1] [outcome.2.2.toNat]
    (getCost 4 state) (getCost 5 state)

theorem packedAssignmentLookupProjection
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (outcome : Nat × Nat × Bool) :
    EvaluatorCodeFits (Code.prepend (Code.get 4) (Code.get 5))
      (Code.packedAssignmentLookupState motif queriedColumn
        target outcome)
      [outcome.2.1, outcome.2.2.toNat]
      (packedAssignmentLookupProjectionCost motif queriedColumn
        target outcome) := by
  simpa [packedAssignmentLookupProjectionCost,
    Code.packedAssignmentLookupState, prependCost] using
    prepend
      (get 4
        (Code.packedAssignmentLookupState motif queriedColumn
          target outcome))
      (get 5
        (Code.packedAssignmentLookupState motif queriedColumn
          target outcome))

set_option maxHeartbeats 800000 in
theorem packedAssignmentLookupProjectionCost_le_linear
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupProjectionCost motif queriedColumn target
        (Code.packedAssignmentLookupOutcome motif queriedColumn
          target word) ≤
      100000000000000000000 *
        (encodedListSpace
          [32 * (Encodable.encode motif +
            Encodable.encode motif + Encodable.encode motif +
            Encodable.encode target + queriedColumn +
            word + 40 + 32) + 200] + 1) := by
  let motifCode := Encodable.encode motif
  let targetCode := Encodable.encode target
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  let limit :=
    32 * (motifCode + motifCode + motifCode +
      targetCode + queriedColumn + word + 40 + 32) + 200
  change
    packedAssignmentLookupProjectionCost motif queriedColumn target
        outcome ≤
      100000000000000000000 *
        (encodedListSpace [limit] + 1)
  have outcomeWord : outcome.1 ≤ word := by
    simpa [outcome] using
      Code.packedAssignmentLookupOutcome_word_le
        motif queriedColumn target word
  have outcomeDigit : outcome.2.1 ≤ 40 := by
    simpa [outcome] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif queriedColumn target word
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have targetBound : targetCode ≤ limit := by
    simp only [limit]
    omega
  have queryBound : queriedColumn ≤ limit := by
    simp only [limit]
    omega
  have wordBound : word ≤ limit := by
    simp only [limit]
    omega
  have outcomeWordBound : outcome.1 ≤ limit :=
    outcomeWord.trans wordBound
  have outcomeDigitBound : outcome.2.1 ≤ limit := by
    simp only [limit]
    omega
  have motifBits := encodeNat_length_mono motifBound
  have targetBits := encodeNat_length_mono targetBound
  have queryBits := encodeNat_length_mono queryBound
  have outcomeWordBits :=
    encodeNat_length_mono outcomeWordBound
  have outcomeDigitBits :=
    encodeNat_length_mono outcomeDigitBound
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have targetSuccBits :=
    encodeNat_length_mono
      (show targetCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have querySuccBits :=
    encodeNat_length_mono
      (show queriedColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have outcomeWordSuccBits :=
    encodeNat_length_mono
      (show outcome.1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have outcomeDigitSuccBits :=
    encodeNat_length_mono
      (show outcome.2.1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  cases outcomeFound : outcome.2.2 <;>
    simp [packedAssignmentLookupProjectionCost,
      Code.packedAssignmentLookupState,
      prependCost, getCost, dropCost, headCost,
      idCost, nilCost, tailCost, zeroPrimeCost,
      succCost, encodedListSpace_cons,
      encodedListSpace_nil, motifCode, targetCode,
      outcomeFound, zeroBits, oneBits, twoBits] at * <;>
    omega

def packedAssignmentLookupCodeCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  packedAssignmentLookupProjectionCost motif queriedColumn
      target outcome +
    (packedAssignmentLookupStagesCost motif queriedColumn target word +
      packedAssignmentLookupInputCost motif queriedColumn target word)

def packedAssignmentLookupSpaceBound
    (motifCode queriedColumn targetCode word : Nat) : Nat :=
  700000000000000000000 *
    (encodedListSpace
      [32 * (motifCode + motifCode + motifCode +
        targetCode + queriedColumn + word + 40 + 32) + 200] + 1)

/-- Native bit-length footprint of one packed assignment query. -/
def packedAssignmentLookupInputUnit
    (motifCode queriedColumn targetCode word : Nat) : Nat :=
  encodedListSpace [motifCode, queriedColumn, targetCode, word] + 1

private theorem packedAssignmentLookupEnvelopeUnit_le_linear
    (motifCode queriedColumn targetCode word : Nat) :
    encodedListSpace
        [32 * (motifCode + motifCode + motifCode +
          targetCode + queriedColumn + word + 40 + 32) + 200] + 1 ≤
      100 * packedAssignmentLookupInputUnit
        motifCode queriedColumn targetCode word := by
  have motifDouble := encodeNat_add_length_le_sum motifCode motifCode
  have motifTriple := encodeNat_add_length_le_sum
    (motifCode + motifCode) motifCode
  have targetSum := encodeNat_add_length_le_sum
    (motifCode + motifCode + motifCode) targetCode
  have columnSum := encodeNat_add_length_le_sum
    (motifCode + motifCode + motifCode + targetCode) queriedColumn
  have wordSum := encodeNat_add_length_le_sum
    (motifCode + motifCode + motifCode + targetCode + queriedColumn) word
  have fortySum := encodeNat_add_length_le_sum
    (motifCode + motifCode + motifCode + targetCode + queriedColumn + word) 40
  have thirtyTwoSum := encodeNat_add_length_le_sum
    (motifCode + motifCode + motifCode + targetCode + queriedColumn + word + 40) 32
  have scaled := encodeNat_mul_length_le_sum 32
    (motifCode + motifCode + motifCode + targetCode +
      queriedColumn + word + 40 + 32)
  have final := encodeNat_add_length_le_sum
    (32 * (motifCode + motifCode + motifCode + targetCode +
      queriedColumn + word + 40 + 32)) 200
  have fortyBits :
      (Computability.encodeNat 40).length = 6 := by native_decide
  have thirtyTwoBits :
      (Computability.encodeNat 32).length = 6 := by native_decide
  have twoHundredBits :
      (Computability.encodeNat 200).length = 8 := by native_decide
  simp only [packedAssignmentLookupInputUnit,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

/-- The established lookup-space envelope is linear in the four query-field
bit lengths. -/
theorem packedAssignmentLookupSpaceBound_le_linear
    (motifCode queriedColumn targetCode word : Nat) :
    packedAssignmentLookupSpaceBound
        motifCode queriedColumn targetCode word ≤
      70000000000000000000000 *
        packedAssignmentLookupInputUnit
          motifCode queriedColumn targetCode word := by
  calc
    packedAssignmentLookupSpaceBound
        motifCode queriedColumn targetCode word =
        700000000000000000000 *
          (encodedListSpace
            [32 * (motifCode + motifCode + motifCode +
              targetCode + queriedColumn + word + 40 + 32) + 200] + 1) := rfl
    _ ≤ 700000000000000000000 *
          (100 * packedAssignmentLookupInputUnit
            motifCode queriedColumn targetCode word) :=
      Nat.mul_le_mul_left _
        (packedAssignmentLookupEnvelopeUnit_le_linear
          motifCode queriedColumn targetCode word)
    _ = 70000000000000000000000 *
          packedAssignmentLookupInputUnit
            motifCode queriedColumn targetCode word := by ring

theorem packedAssignmentLookupCodeCost_le_linear
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupCodeCost motif queriedColumn target word ≤
      packedAssignmentLookupSpaceBound
        (Encodable.encode motif) queriedColumn
        (Encodable.encode target) word := by
  have stages :=
    packedAssignmentLookupStagesCost_le_linear
      motif queriedColumn target word
  have input :=
    packedAssignmentLookupInputCost_le_linear
      motif queriedColumn target word
  have projection :=
    packedAssignmentLookupProjectionCost_le_linear
      motif queriedColumn target word
  simp only [packedAssignmentLookupCodeCost,
    packedAssignmentLookupSpaceBound]
  omega

theorem packedAssignmentLookup
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [(Code.packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1,
        (Code.packedAssignmentLookupOutcome motif queriedColumn
          target word).2.2.toNat]
      (packedAssignmentLookupCodeCost motif queriedColumn
        target word) := by
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  have stages :=
    comp
      (packedAssignmentLookupStages motif queriedColumn target word)
      (packedAssignmentLookupInput motif queriedColumn target word)
  have result :=
    comp
      (packedAssignmentLookupProjection motif queriedColumn
        target outcome)
      stages
  simpa [Code.packedAssignmentLookupCode,
    packedAssignmentLookupCodeCost, outcome] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
