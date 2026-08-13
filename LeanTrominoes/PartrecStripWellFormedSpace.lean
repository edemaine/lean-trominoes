/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecStripWellFormed
import LeanTrominoes.PartrecStripCellBoundsSpace
import LeanTrominoes.PartrecEncodedListDecodeSpace
import LeanTrominoes.PartrecPeriodicStripDecodeSpace
import LeanTrominoes.PartrecNatCompareSpace

/-!
# Evaluator-space certificate for strip well-formedness

This module first fits every reachable typed motif step and then lifts those
certificates through the flat countdown using its reachable-state rule.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def stripMotifViewCost
    (width period : Nat) (valid : Bool)
    (motif : List Cell) : Nat :=
  encodedListViewCost motif +
    getCost 0
      (Code.stripMotifState width period valid motif)

theorem stripMotifView
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits Code.stripMotifViewCode
      (Code.stripMotifState width period valid motif)
      (match motif with
      | [] => [0, 0, 0]
      | cell :: remaining =>
          [1, Encodable.encode cell,
            Encodable.encode remaining])
      (stripMotifViewCost width period valid motif) := by
  cases motif with
  | nil =>
      simpa [Code.stripMotifViewCode,
        stripMotifViewCost] using
        comp (encodedListView ([] : List Cell))
          (get 0
            (Code.stripMotifState width period valid []))
  | cons cell remaining =>
      simpa [Code.stripMotifViewCode,
        stripMotifViewCost] using
        comp (encodedListView (cell :: remaining))
          (get 0
            (Code.stripMotifState width period valid
              (cell :: remaining)))

def stripMotifHeadCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 1
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    stripMotifViewCost width period valid
      (cell :: remaining)

theorem stripMotifHeadCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.stripMotifHeadCellCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [Encodable.encode cell]
      (stripMotifHeadCellCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifHeadCellCode,
    stripMotifHeadCellCost] using
    comp
      (get 1
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (stripMotifView width period valid
        (cell :: remaining))

def stripMotifTailCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 2
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    stripMotifViewCost width period valid
      (cell :: remaining)

theorem stripMotifTail
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.stripMotifTailCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [Encodable.encode remaining]
      (stripMotifTailCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifTailCode,
    stripMotifTailCost] using
    comp
      (get 2
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (stripMotifView width period valid
        (cell :: remaining))

def stripMotifPeriodAndCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  prependCost state [period] [Encodable.encode cell]
    (getCost 3 state)
    (stripMotifHeadCellCost
      width period valid cell remaining)

theorem stripMotifPeriodAndCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 3)
        Code.stripMotifHeadCellCode)
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [period, Encodable.encode cell]
      (stripMotifPeriodAndCellCost
        width period valid cell remaining) := by
  simpa [stripMotifPeriodAndCellCost,
    prependCost, Code.stripMotifState] using
    prepend
      (get 3
        (Code.stripMotifState width period valid
          (cell :: remaining)))
      (stripMotifHeadCell width period valid
        cell remaining)

def stripMotifCellArgumentsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  prependCost state [width]
    [period, Encodable.encode cell]
    (getCost 2 state)
    (stripMotifPeriodAndCellCost
      width period valid cell remaining)

theorem stripMotifCellArguments
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      Code.stripMotifCellArgumentsCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [width, period, Encodable.encode cell]
      (stripMotifCellArgumentsCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifCellArgumentsCode,
    stripMotifCellArgumentsCost, prependCost,
    Code.stripMotifState] using
    prepend
      (get 2
        (Code.stripMotifState width period valid
          (cell :: remaining)))
      (stripMotifPeriodAndCell width period valid
        cell remaining)

def stripMotifHeadInBoundsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  stripCellInBoundsCost width period cell +
    stripMotifCellArgumentsCost
      width period valid cell remaining

theorem stripMotifHeadInBounds
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      Code.stripMotifHeadInBoundsCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [if cell.InStripBounds width period then 1 else 0]
      (stripMotifHeadInBoundsCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifHeadInBoundsCode,
    stripMotifHeadInBoundsCost] using
    comp (stripCellInBounds width period cell)
      (stripMotifCellArguments width period valid
        cell remaining)

def stripMotifUpdatedValidCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  let cellTag :=
    if cell.InStripBounds width period then 1 else 0
  boolAndCost state valid.toNat cellTag
    (getCost 1 state)
    (stripMotifHeadInBoundsCost
      width period valid cell remaining)

theorem stripMotifUpdatedValid
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      Code.stripMotifUpdatedValidCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [(valid &&
        decide (cell.InStripBounds width period)).toNat]
      (stripMotifUpdatedValidCost
        width period valid cell remaining) := by
  have combined :=
    boolAnd
      (get 1
        (Code.stripMotifState width period valid
          (cell :: remaining)))
      (stripMotifHeadInBounds width period valid
        cell remaining)
  cases valid <;>
    by_cases inBounds :
      cell.InStripBounds width period <;>
    simpa [Code.stripMotifUpdatedValidCode,
      stripMotifUpdatedValidCost,
      Code.stripMotifState, inBounds] using combined

def stripMotifDimensionsCost
    (width period : Nat) (valid : Bool)
    (motif : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid motif
  prependCost state [width] [period]
    (getCost 2 state) (getCost 3 state)

theorem stripMotifDimensions
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) (Code.get 3))
      (Code.stripMotifState width period valid motif)
      [width, period]
      (stripMotifDimensionsCost
        width period valid motif) := by
  simpa [stripMotifDimensionsCost,
    prependCost, Code.stripMotifState] using
    prepend
      (get 2
        (Code.stripMotifState width period valid motif))
      (get 3
        (Code.stripMotifState width period valid motif))

def stripMotifValidAndDimensionsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  let nextValid :=
    valid && decide (cell.InStripBounds width period)
  prependCost state [nextValid.toNat] [width, period]
    (stripMotifUpdatedValidCost
      width period valid cell remaining)
    (stripMotifDimensionsCost
      width period valid (cell :: remaining))

theorem stripMotifValidAndDimensions
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    let nextValid :=
      valid && decide (cell.InStripBounds width period)
    EvaluatorCodeFits
      (Code.prepend Code.stripMotifUpdatedValidCode
        (Code.prepend (Code.get 2) (Code.get 3)))
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [nextValid.toNat, width, period]
      (stripMotifValidAndDimensionsCost
        width period valid cell remaining) := by
  simpa [stripMotifValidAndDimensionsCost,
    prependCost] using
    prepend
      (stripMotifUpdatedValid width period valid
        cell remaining)
      (stripMotifDimensions width period valid
        (cell :: remaining))

def stripMotifConsStepCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  let nextValid :=
    valid && decide (cell.InStripBounds width period)
  prependCost state [Encodable.encode remaining]
    [nextValid.toNat, width, period]
    (stripMotifTailCost
      width period valid cell remaining)
    (stripMotifValidAndDimensionsCost
      width period valid cell remaining)

theorem stripMotifConsStep
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    let nextValid :=
      valid && decide (cell.InStripBounds width period)
    EvaluatorCodeFits Code.stripMotifConsStepCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      (Code.stripMotifState width period
        nextValid remaining)
      (stripMotifConsStepCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifConsStepCode,
    stripMotifConsStepCost, prependCost,
    Code.stripMotifState] using
    prepend
      (stripMotifTail width period valid
        cell remaining)
      (stripMotifValidAndDimensions width period valid
        cell remaining)

def stripMotifStepCost
    (width period : Nat) (valid : Bool) :
    List Cell → Nat
  | [] =>
      let state :=
        Code.stripMotifState width period valid []
      branchZeroZeroCost state state 0
        (getCost 0 state) (idCost state)
  | cell :: remaining =>
      let state :=
        Code.stripMotifState width period valid
          (cell :: remaining)
      let nextValid :=
        valid && decide (cell.InStripBounds width period)
      branchZeroSuccCost state
        (Code.stripMotifState width period
          nextValid remaining)
        (Encodable.encode (cell :: remaining))
        (getCost 0 state)
        (stripMotifConsStepCost
          width period valid cell remaining)

theorem stripMotifStep
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits Code.stripMotifStepCode
      (Code.stripMotifState width period valid motif)
      (Code.stripMotifNativeStep
        (Code.stripMotifState width period valid motif))
      (stripMotifStepCost
        width period valid motif) := by
  cases motif with
  | nil =>
      simpa [Code.stripMotifStepCode,
        stripMotifStepCost] using
        branchZero_zero rfl
          (get 0
            (Code.stripMotifState width period valid []))
          (id
            (Code.stripMotifState width period valid []))
  | cons cell remaining =>
      have positive :
          0 < Encodable.encode (cell :: remaining) := by
        simp
      simpa [Code.stripMotifStepCode,
        stripMotifStepCost] using
        branchZero_succ positive
          (get 0
            (Code.stripMotifState width period valid
              (cell :: remaining)))
          (stripMotifConsStep width period valid
            cell remaining)

def stripMotifBodyCost
    (remaining width period : Nat)
    (valid : Bool) (motif : List Cell) : Nat :=
  flatCountdownBodyCost Code.stripMotifNativeStep
    (fun _ =>
      stripMotifStepCost width period valid motif)
    remaining
    (Code.stripMotifState width period valid motif)

theorem stripMotifBody
    (remaining width period : Nat)
    (valid : Bool) (motif : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.stripMotifStepCode)
      (remaining ::
        Code.stripMotifState width period valid motif)
      (flatCountdownOutput Code.stripMotifNativeStep
        remaining
        (Code.stripMotifState width period valid motif))
      (stripMotifBodyCost
        remaining width period valid motif) := by
  cases remaining with
  | zero =>
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, stripMotifBodyCost,
        flatCountdownBodyCost, zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one
              (.cons Code.head
                (Code.stripMotifStepCode.comp Code.tail)))
          (values :=
            0 ::
              Code.stripMotifState
                width period valid motif)
          (by rfl)
          (zero'_named
            (Code.stripMotifState
              width period valid motif))
  | succ remaining =>
      let payload :=
        Code.stripMotifState width period valid motif
      let values := remaining :: payload
      have transformed :=
        comp (stripMotifStep width period valid motif)
          (tail_named values)
      have payloadResult :=
        prepend (head values) transformed
      have branch :=
        prepend (one values) payloadResult
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, stripMotifBodyCost,
        flatCountdownBodyCost,
        flatCountdownSuccBranchCost,
        payload, values, prependCost,
        Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values :=
            (remaining + 1) :: payload)
          (predecessor := remaining)
          (by rfl) branch

set_option maxHeartbeats 800000 in
theorem stripMotifBodyCost_le_linear
    (steps width period : Nat) (valid : Bool)
    (motif : List Cell) :
    stripMotifBodyCost steps width period valid motif ≤
      500000000000 *
        (encodedListSpace
          [2 * (steps + width + period +
            Encodable.encode motif) + 4] + 1) := by
  let motifCode := Encodable.encode motif
  let limit :=
    2 * (steps + width + period + motifCode) + 4
  have stepsBound : steps ≤ limit := by
    simp only [limit]
    omega
  have widthBound : width ≤ limit := by
    simp only [limit]
    omega
  have periodBound : period ≤ limit := by
    simp only [limit]
    omega
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have stepsBits := encodeNat_length_mono stepsBound
  have stepsPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le steps).trans stepsBound)
  have widthBits := encodeNat_length_mono widthBound
  have periodBits := encodeNat_length_mono periodBound
  have motifBits := encodeNat_length_mono motifBound
  have stepsSuccBits :=
    encodeNat_length_mono
      (show steps + 1 ≤ limit by
        simp only [limit]
        omega)
  have widthSuccBits :=
    encodeNat_length_mono
      (show width + 1 ≤ limit by
        simp only [limit]
        omega)
  have periodSuccBits :=
    encodeNat_length_mono
      (show period + 1 ≤ limit by
        simp only [limit]
        omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have viewBound := encodedListViewCost_le_linear motif
  have viewLimit :
      encodedListSpace [2 * Encodable.encode motif + 4] ≤
        encodedListSpace [limit] := by
    have numeric :
        2 * Encodable.encode motif + 4 ≤ limit := by
      simp only [limit, motifCode]
      omega
    simpa only [encodedListSpace_cons,
      encodedListSpace_nil, Nat.add_le_add_iff_right] using
      encodeNat_length_mono numeric
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have fourBits :
      (Computability.encodeNat 4).length = 3 := rfl
  have fourLimitBits :=
    encodeNat_length_mono
      (show 4 ≤ limit by
        simp only [limit]
        omega)
  have validBits :
      (Computability.encodeNat valid.toNat).length ≤
        (Computability.encodeNat limit).length := by
    cases valid with
    | false =>
        simp [zeroBits]
    | true =>
        simp only [Bool.toNat_true, oneBits]
        have atLeastThree :
            3 ≤ (Computability.encodeNat limit).length := by
          simpa [fourBits] using fourLimitBits
        omega
  cases motif with
  | nil =>
      cases steps <;>
        simp [stripMotifBodyCost,
          stripMotifStepCost, Code.stripMotifState,
          flatCountdownBodyCost,
          flatCountdownSuccBranchCost,
          branchZeroZeroCost, branchZeroTestCost,
          prependCost, getCost, dropCost, idCost,
          headCost, nilCost, oneCost, zeroCost,
          zeroPrimeCost, tailCost, succCost,
          Code.stripMotifNativeStep,
          encodedListSpace_cons, encodedListSpace_nil,
          motifCode, limit, zeroBits, oneBits,
          twoBits, fourBits] at * <;>
        omega
  | cons cell remaining =>
      let cellCode := Encodable.encode cell
      let tailCode := Encodable.encode remaining
      have cellMotif :
          cellCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons,
          cellCode]
        exact (Nat.left_le_pair cellCode tailCode).trans
          (Nat.le_succ _)
      have tailMotif :
          tailCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons,
          tailCode]
        exact (Nat.right_le_pair cellCode tailCode).trans
          (Nat.le_succ _)
      have cellLimit :
          cellCode ≤ limit :=
        cellMotif.trans (by simpa [motifCode] using motifBound)
      have tailLimit :
          tailCode ≤ limit :=
        tailMotif.trans (by simpa [motifCode] using motifBound)
      have cellBits := encodeNat_length_mono cellLimit
      have tailBits := encodeNat_length_mono tailLimit
      have constructorBits :=
        encodeNat_length_mono
          (show Nat.pair cellCode tailCode ≤ limit by
            exact (Nat.le_succ _).trans
              (by simpa [motifCode] using motifBound))
      have cellSuccBits :=
        encodeNat_length_mono
          (show cellCode + 1 ≤ limit by
            simp only [limit]
            omega)
      have tailSuccBits :=
        encodeNat_length_mono
          (show tailCode + 1 ≤ limit by
            simp only [limit]
            omega)
      have cellPredicateBound :=
        stripCellInBoundsCost_le_linear width period cell
      have cellPredicateLimit :
          encodedListSpace
              [2 * (width + period + Encodable.encode cell) + 4] ≤
            encodedListSpace [limit] := by
        have numeric :
            2 * (width + period + Encodable.encode cell) + 4 ≤
              limit := by
          simp only [limit, motifCode]
          omega
        simpa only [encodedListSpace_cons,
          encodedListSpace_nil, Nat.add_le_add_iff_right] using
          encodeNat_length_mono numeric
      cases steps with
      | zero =>
          simp [stripMotifBodyCost,
            flatCountdownBodyCost, zeroPrimeCost,
            Code.stripMotifState,
          encodedListSpace_cons, encodedListSpace_nil,
          motifCode, limit, zeroBits, oneBits,
          twoBits, fourBits] at *
          omega
      | succ steps =>
          cases valid <;>
            by_cases inBounds :
              cell.InStripBounds width period <;>
            simp [stripMotifBodyCost,
              stripMotifStepCost, stripMotifConsStepCost,
              stripMotifValidAndDimensionsCost,
              stripMotifUpdatedValidCost,
              stripMotifHeadInBoundsCost,
              stripMotifCellArgumentsCost,
              stripMotifPeriodAndCellCost,
              stripMotifHeadCellCost,
              stripMotifTailCost, stripMotifViewCost,
              stripMotifDimensionsCost,
              Code.stripMotifState,
              flatCountdownBodyCost,
              flatCountdownSuccBranchCost,
              branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, boolAndCost,
              normalizeBoolCost, prependCost,
              getCost, dropCost, idCost, headCost,
              nilCost, oneCost, zeroCost,
              zeroPrimeCost, tailCost, succCost,
              Code.stripMotifNativeStep,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, cellCode, tailCode, limit,
              inBounds, zeroBits, oneBits,
              twoBits, fourBits] at * <;>
            omega

theorem encode_list_suffix_le
    {α : Type*} [Encodable α]
    (leading suffix : List α) :
    Encodable.encode suffix ≤
      Encodable.encode (leading ++ suffix) := by
  induction leading with
  | nil =>
      simp
  | cons value leading induction =>
      simp only [List.cons_append,
        Encodable.encode_list_cons]
      exact induction.trans
        ((Nat.right_le_pair
          (Encodable.encode value)
          (Encodable.encode (leading ++ suffix))).trans
            (Nat.le_succ _))

def stripMotifSpaceBound
    (encodedStrip : Nat) : Nat :=
  100000000000000 *
    (encodedListSpace [encodedStrip] + 1)

theorem stripMotifBodyCost_le_stripInput
    (periodicStrip : PeriodicStrip)
    (steps : Nat) (valid : Bool)
    (motif : List Cell)
    (stepsBound :
      steps ≤ Encodable.encode periodicStrip.motif)
    (suffixBound :
      Encodable.encode motif ≤
        Encodable.encode periodicStrip.motif) :
    stripMotifBodyCost steps periodicStrip.width
        periodicStrip.period valid motif ≤
      stripMotifSpaceBound
        (Encodable.encode periodicStrip) := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let localLimit :=
    2 * (steps + periodicStrip.width +
      periodicStrip.period + Encodable.encode motif) + 4
  have widthStrip :
      periodicStrip.width ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact Nat.left_le_pair _ _
  have periodStrip :
      periodicStrip.period ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact (Nat.left_le_pair _ _).trans
      (Nat.right_le_pair _ _)
  have motifStrip : motifCode ≤ stripCode := by
    simp only [motifCode, stripCode,
      PeriodicStrip.encode_eq_pair]
    exact (Nat.right_le_pair _ _).trans
      (Nat.right_le_pair _ _)
  have localNumeric :
      localLimit ≤ 8 * stripCode + 4 := by
    simp only [localLimit]
    omega
  have localBits :=
    encodeNat_length_mono localNumeric
  have scaledBits :=
    encodeNat_eight_mul_add_four_length_le stripCode
  have body :=
    stripMotifBodyCost_le_linear
      steps periodicStrip.width periodicStrip.period
      valid motif
  simp only [stripMotifSpaceBound,
    encodedListSpace_cons, encodedListSpace_nil] at body ⊢
  change
    stripMotifBodyCost steps periodicStrip.width
        periodicStrip.period valid motif ≤
      100000000000000 *
        ((Computability.encodeNat stripCode).length + 1 + 1)
  change
    stripMotifBodyCost steps periodicStrip.width
        periodicStrip.period valid motif ≤
      100000000000000 *
        ((Computability.encodeNat stripCode).length + 2)
  change
    stripMotifBodyCost steps periodicStrip.width
        periodicStrip.period valid motif ≤
      _ at body
  have localIdentity :
      2 * (steps + periodicStrip.width +
          periodicStrip.period + Encodable.encode motif) + 4 =
        localLimit := rfl
  rw [localIdentity] at body
  omega

/-- Typed suffix states reachable while the motif countdown is running. -/
def StripMotifReachable
    (periodicStrip : PeriodicStrip)
    (steps : Nat) (values : List Nat) : Prop :=
  ∃ valid motif leading,
    values =
      Code.stripMotifState periodicStrip.width
        periodicStrip.period valid motif ∧
    steps ≤ Encodable.encode periodicStrip.motif ∧
    periodicStrip.motif = leading ++ motif

theorem stripMotifReachable_initial
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    StripMotifReachable periodicStrip
      (Encodable.encode periodicStrip.motif)
      (Code.stripMotifState periodicStrip.width
        periodicStrip.period valid periodicStrip.motif) := by
  exact ⟨valid, periodicStrip.motif, [],
    rfl, Nat.le_refl _, by simp⟩

theorem stripMotifReachable_step
    (periodicStrip : PeriodicStrip)
    (steps : Nat) (values : List Nat)
    (reachable :
      StripMotifReachable periodicStrip (steps + 1) values) :
    StripMotifReachable periodicStrip steps
      (Code.stripMotifNativeStep values) := by
  obtain ⟨valid, motif, leading, rfl,
    stepsBound, suffix⟩ := reachable
  cases motif with
  | nil =>
      exact ⟨valid, [], leading,
        Code.stripMotifNativeStep_state_nil
          periodicStrip.width periodicStrip.period valid,
        by omega, suffix⟩
  | cons cell motif =>
      refine
        ⟨valid &&
            decide
              (cell.InStripBounds periodicStrip.width
                periodicStrip.period),
          motif, leading ++ [cell], ?_, by omega, ?_⟩
      · exact
          Code.stripMotifNativeStep_state_cons
            periodicStrip.width periodicStrip.period
            valid cell motif
      · simpa [List.append_assoc] using suffix

/-- The motif loop reuses one input-linear workspace allowance at every
reachable step instead of summing that allowance over the numeric countdown.
-/
theorem stripMotifFlatUniform
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    EvaluatorCodeFits
      (Code.flatIterate Code.stripMotifStepCode)
      (Encodable.encode periodicStrip.motif ::
        Code.stripMotifState periodicStrip.width
          periodicStrip.period valid periodicStrip.motif)
      (Code.stripMotifState periodicStrip.width
        periodicStrip.period
        (valid &&
          motifInStripBounds periodicStrip.width
            periodicStrip.period periodicStrip.motif) [])
      (stripMotifSpaceBound
        (Encodable.encode periodicStrip)) where
  input_space := by
    have body :=
      stripMotifBody
        (Encodable.encode periodicStrip.motif)
        periodicStrip.width periodicStrip.period
        valid periodicStrip.motif
    exact body.input_space.trans
      (stripMotifBodyCost_le_stripInput periodicStrip
        (Encodable.encode periodicStrip.motif)
        valid periodicStrip.motif
        (Nat.le_refl _) (Nat.le_refl _))
  output_space := by
    let result :=
      valid &&
        motifInStripBounds periodicStrip.width
          periodicStrip.period periodicStrip.motif
    have body :=
      stripMotifBody 0 periodicStrip.width
        periodicStrip.period result []
    have input := body.input_space
    have cost :=
      stripMotifBodyCost_le_stripInput periodicStrip
        0 result [] (Nat.zero_le _)
        (by
          exact (Nat.zero_le _).trans
            (show
              Encodable.encode ([] : List Cell) ≤
                Encodable.encode periodicStrip.motif
              by simp))
    simp only [result] at input cost
    simp only [Code.stripMotifState,
      encodedListSpace_cons] at input ⊢
    omega
  call continuation bound budget after := by
    apply
      EvaluatorCallFits.flatIterate_of_reachable_code_fits
        (step := Code.stripMotifNativeStep)
        (bodyCost := fun _ _ =>
          stripMotifSpaceBound
            (Encodable.encode periodicStrip))
        (invariant := StripMotifReachable periodicStrip)
    · intro steps values reachable
      obtain ⟨reachableValid, reachableMotif, leading,
        rfl, stepsBound, suffix⟩ := reachable
      exact
        (stripMotifBody steps periodicStrip.width
          periodicStrip.period reachableValid
          reachableMotif).mono
          (stripMotifBodyCost_le_stripInput periodicStrip
            steps reachableValid reachableMotif stepsBound
            (by
              rw [suffix]
              exact encode_list_suffix_le leading reachableMotif))
    · exact stripMotifReachable_initial periodicStrip valid
    · exact stripMotifReachable_step periodicStrip
    · intro steps values reachable
      exact budget
    · rw [Code.stripMotifNativeStep_iterate,
        Code.stripMotifProcess_encode]
      exact after

/-- Sum of the fitted body costs along the unique typed motif run. -/
def stripMotifFlatCost
    (width period : Nat) :
    Nat → Bool → List Cell → Nat
  | 0, valid, motif =>
      stripMotifBodyCost 0 width period valid motif
  | remaining + 1, valid, [] =>
      stripMotifBodyCost (remaining + 1)
          width period valid [] +
        stripMotifFlatCost width period
          remaining valid []
  | remaining + 1, valid, cell :: motif =>
      let nextValid :=
        valid && decide (cell.InStripBounds width period)
      stripMotifBodyCost (remaining + 1)
          width period valid (cell :: motif) +
        stripMotifFlatCost width period
          remaining nextValid motif

theorem stripMotifBodyCost_le_flatCost
    (width period steps : Nat) (valid : Bool)
    (motif : List Cell) :
    stripMotifBodyCost steps width period valid motif ≤
      stripMotifFlatCost width period steps valid motif := by
  cases steps with
  | zero =>
      simp [stripMotifFlatCost]
  | succ steps =>
      cases motif <;> simp [stripMotifFlatCost]

theorem stripMotifProcessSpace_le_flatCost
    (width period steps : Nat) (valid : Bool)
    (motif : List Cell) :
    encodedListSpace
        (Code.stripMotifProcess width period
          steps valid motif) ≤
      stripMotifFlatCost width period steps valid motif := by
  induction steps generalizing valid motif with
  | zero =>
      have output :=
        (stripMotifBody 0 width period valid motif).output_space
      simp [flatCountdownOutput,
        Code.stripMotifProcess,
        stripMotifFlatCost] at output ⊢
      omega
  | succ steps induction =>
      cases motif with
      | nil =>
          exact (induction valid []).trans
            (by simp [stripMotifFlatCost])
      | cons cell motif =>
          let nextValid :=
            valid && decide (cell.InStripBounds width period)
          exact (induction nextValid motif).trans
            (by
              simp [stripMotifFlatCost, nextValid])

theorem stripMotifFlat
    (width period steps : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits
      (Code.flatIterate Code.stripMotifStepCode)
      (steps ::
        Code.stripMotifState width period valid motif)
      (Code.stripMotifProcess width period
        steps valid motif)
      (stripMotifFlatCost
        width period steps valid motif) where
  input_space := by
    exact
      (stripMotifBody
        steps width period valid motif).input_space.trans
        (stripMotifBodyCost_le_flatCost
          width period steps valid motif)
  output_space :=
    stripMotifProcessSpace_le_flatCost
      width period steps valid motif
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction steps generalizing valid motif with
    | zero =>
        let payload :=
          Code.stripMotifState width period valid motif
        have body :=
          stripMotifBody 0 width period valid motif
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    Code.stripMotifStepCode)
                  continuation)
                (flatCountdownOutput
                  Code.stripMotifNativeStep 0 payload)) := by
          apply EvaluatorExecutionFits.ret_fix_zero
          · rfl
          · simp only [continuationSpace_fix]
            have output := body.output_space
            change
              encodedListSpace
                  (flatCountdownOutput
                    Code.stripMotifNativeStep 0
                    (Code.stripMotifState
                      width period valid motif)) +
                  continuationSpace continuation ≤
                bound
            simp only [stripMotifFlatCost] at budget
            omega
          · simpa [flatCountdownOutput,
              Code.stripMotifProcess, payload] using after
        exact body.call
          (.fix
            (Code.flatCountdownBody
              Code.stripMotifStepCode)
            continuation)
          bound
          (by
            simp only [continuationSpace_fix,
              stripMotifFlatCost] at *
            exact budget)
          fixedAfter
    | succ steps induction =>
        cases motif with
        | nil =>
            let payload :=
              Code.stripMotifState width period valid []
            have body :=
              stripMotifBody (steps + 1)
                width period valid []
            have recursiveBudget :
                stripMotifFlatCost width period steps valid [] +
                    continuationSpace continuation ≤
                  bound := by
              simp only [stripMotifFlatCost] at budget
              omega
            have recursiveAfter :
                EvaluatorExecutionFits bound
                  (.ret continuation
                    (Code.stripMotifProcess width period
                      steps valid [])) := by
              simpa [Code.stripMotifProcess] using after
            have recursiveBody :=
              induction valid [] recursiveBudget recursiveAfter
            have fixedAfter :
                EvaluatorExecutionFits bound
                  (.ret
                    (.fix
                      (Code.flatCountdownBody
                        Code.stripMotifStepCode)
                      continuation)
                    (flatCountdownOutput
                      Code.stripMotifNativeStep
                      (steps + 1) payload)) := by
              apply EvaluatorExecutionFits.ret_fix_succ
              · simp [flatCountdownOutput, payload]
              · simp only [continuationSpace_fix]
                have output := body.output_space
                change
                  encodedListSpace
                      (flatCountdownOutput
                        Code.stripMotifNativeStep
                        (steps + 1)
                        (Code.stripMotifState
                          width period valid [])) +
                      continuationSpace continuation ≤
                    bound
                simp only [stripMotifFlatCost] at budget
                omega
              · simpa [flatCountdownOutput, payload] using
                  recursiveBody
            exact body.call
              (.fix
                (Code.flatCountdownBody
                  Code.stripMotifStepCode)
                continuation)
              bound
              (by
                simp only [continuationSpace_fix,
                  stripMotifFlatCost] at *
                omega)
              fixedAfter
        | cons cell motif =>
            let nextValid :=
              valid && decide (cell.InStripBounds width period)
            let payload :=
              Code.stripMotifState width period valid
                (cell :: motif)
            have body :=
              stripMotifBody (steps + 1)
                width period valid (cell :: motif)
            have recursiveBudget :
                stripMotifFlatCost width period
                    steps nextValid motif +
                    continuationSpace continuation ≤
                  bound := by
              have raw :
                  stripMotifFlatCost width period steps
                        (valid &&
                          decide
                            (cell.InStripBounds width period))
                        motif +
                      continuationSpace continuation ≤
                    bound := by
                simp only [stripMotifFlatCost] at budget
                omega
              simpa only [nextValid] using raw
            have recursiveAfter :
                EvaluatorExecutionFits bound
                  (.ret continuation
                    (Code.stripMotifProcess width period
                      steps nextValid motif)) := by
              simpa [Code.stripMotifProcess,
                nextValid] using after
            have recursiveBody :=
              induction nextValid motif
                recursiveBudget recursiveAfter
            have fixedAfter :
                EvaluatorExecutionFits bound
                  (.ret
                    (.fix
                      (Code.flatCountdownBody
                        Code.stripMotifStepCode)
                      continuation)
                    (flatCountdownOutput
                      Code.stripMotifNativeStep
                      (steps + 1) payload)) := by
              apply EvaluatorExecutionFits.ret_fix_succ
              · simp [flatCountdownOutput, payload]
              · simp only [continuationSpace_fix]
                have output := body.output_space
                change
                  encodedListSpace
                      (flatCountdownOutput
                        Code.stripMotifNativeStep
                        (steps + 1)
                        (Code.stripMotifState width period valid
                          (cell :: motif))) +
                      continuationSpace continuation ≤
                    bound
                simp only [stripMotifFlatCost] at budget
                omega
              · simpa [flatCountdownOutput, payload,
                  nextValid] using recursiveBody
            exact body.call
              (.fix
                (Code.flatCountdownBody
                  Code.stripMotifStepCode)
                continuation)
              bound
              (by
                simp only [continuationSpace_fix,
                  stripMotifFlatCost] at *
                omega)
              fixedAfter

def stripDimensionWidthCost
    (width period motifCode : Nat) : Nat :=
  natPositiveCost width +
    getCost 0 [width, period, motifCode]

theorem stripDimensionWidth
    (width period motifCode : Nat) :
    EvaluatorCodeFits
      (Code.natPositiveCode.comp (Code.get 0))
      [width, period, motifCode]
      [(decide (0 < width)).toNat]
      (stripDimensionWidthCost width period motifCode) := by
  by_cases positive : 0 < width <;>
    simpa [stripDimensionWidthCost, positive] using
      comp (natPositive width)
        (get 0 [width, period, motifCode])

def stripDimensionPeriodCost
    (width period motifCode : Nat) : Nat :=
  natPositiveCost period +
    getCost 1 [width, period, motifCode]

theorem stripDimensionPeriod
    (width period motifCode : Nat) :
    EvaluatorCodeFits
      (Code.natPositiveCode.comp (Code.get 1))
      [width, period, motifCode]
      [(decide (0 < period)).toNat]
      (stripDimensionPeriodCost width period motifCode) := by
  by_cases positive : 0 < period <;>
    simpa [stripDimensionPeriodCost, positive] using
      comp (natPositive period)
        (get 1 [width, period, motifCode])

def stripDimensionsValidCost
    (width period motifCode : Nat) : Nat :=
  boolAndCost [width, period, motifCode]
    (decide (0 < width)).toNat
    (decide (0 < period)).toNat
    (stripDimensionWidthCost width period motifCode)
    (stripDimensionPeriodCost width period motifCode)

theorem stripDimensionsValid
    (width period motifCode : Nat) :
    EvaluatorCodeFits Code.stripDimensionsValidCode
      [width, period, motifCode]
      [(decide (0 < width) &&
        decide (0 < period)).toNat]
      (stripDimensionsValidCost
        width period motifCode) := by
  have fitted :=
    boolAnd
      (stripDimensionWidth width period motifCode)
      (stripDimensionPeriod width period motifCode)
  by_cases widthPositive : 0 < width <;>
    by_cases periodPositive : 0 < period <;>
    simpa [Code.stripDimensionsValidCode,
      stripDimensionsValidCost,
      widthPositive, periodPositive] using fitted

def stripWellFormedDimensionHeaderCost
    (width period motifCode : Nat) : Nat :=
  prependCost [width, period, motifCode]
    [(decide (0 < width) &&
      decide (0 < period)).toNat]
    [width, period]
    (stripDimensionsValidCost width period motifCode)
    (prependCost [width, period, motifCode]
      [width] [period]
      (getCost 0 [width, period, motifCode])
      (getCost 1 [width, period, motifCode]))

theorem stripWellFormedDimensionHeader
    (width period motifCode : Nat) :
    EvaluatorCodeFits
      (Code.prepend Code.stripDimensionsValidCode <|
        Code.prepend (Code.get 0) (Code.get 1))
      [width, period, motifCode]
      [(decide (0 < width) &&
          decide (0 < period)).toNat,
        width, period]
      (stripWellFormedDimensionHeaderCost
        width period motifCode) := by
  have header :=
    prepend
      (get 0 [width, period, motifCode])
      (get 1 [width, period, motifCode])
  simpa [stripWellFormedDimensionHeaderCost,
    prependCost] using
    prepend
      (stripDimensionsValid width period motifCode)
      header

def stripWellFormedPayloadCost
    (width period motifCode : Nat) : Nat :=
  prependCost [width, period, motifCode]
    [motifCode]
    [(decide (0 < width) &&
        decide (0 < period)).toNat,
      width, period]
    (getCost 2 [width, period, motifCode])
    (stripWellFormedDimensionHeaderCost
      width period motifCode)

theorem stripWellFormedPayload
    (width period motifCode : Nat) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) <|
        Code.prepend Code.stripDimensionsValidCode <|
          Code.prepend (Code.get 0) (Code.get 1))
      [width, period, motifCode]
      [motifCode,
        (decide (0 < width) &&
          decide (0 < period)).toNat,
        width, period]
      (stripWellFormedPayloadCost
        width period motifCode) := by
  simpa [stripWellFormedPayloadCost,
    prependCost] using
    prepend
      (get 2 [width, period, motifCode])
      (stripWellFormedDimensionHeader
        width period motifCode)

def stripWellFormedLoopInputCost
    (width period motifCode : Nat) : Nat :=
  prependCost [width, period, motifCode]
    [motifCode]
    [motifCode,
      (decide (0 < width) &&
        decide (0 < period)).toNat,
      width, period]
    (getCost 2 [width, period, motifCode])
    (stripWellFormedPayloadCost width period motifCode)

theorem stripWellFormedLoopInput
    (width period motifCode : Nat) :
    EvaluatorCodeFits Code.stripWellFormedLoopInputCode
      [width, period, motifCode]
      [motifCode, motifCode,
        (decide (0 < width) &&
          decide (0 < period)).toNat,
        width, period]
      (stripWellFormedLoopInputCost
        width period motifCode) := by
  simpa [Code.stripWellFormedLoopInputCode,
    stripWellFormedLoopInputCost, prependCost] using
    prepend
      (get 2 [width, period, motifCode])
      (stripWellFormedPayload width period motifCode)

def stripWellFormedLoopCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  stripMotifFlatCost periodicStrip.width
      periodicStrip.period
      (Encodable.encode periodicStrip.motif)
      dimensionsValid periodicStrip.motif +
    stripWellFormedLoopInputCost periodicStrip.width
      periodicStrip.period
      (Encodable.encode periodicStrip.motif)

theorem stripWellFormedLoop
    (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) &&
        decide (0 < periodicStrip.period)
    EvaluatorCodeFits
      ((Code.flatIterate Code.stripMotifStepCode).comp
        Code.stripWellFormedLoopInputCode)
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif]
      (Code.stripMotifState periodicStrip.width
        periodicStrip.period
        (dimensionsValid &&
          motifInStripBounds periodicStrip.width
            periodicStrip.period periodicStrip.motif) [])
      (stripWellFormedLoopCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  have loop :=
    stripMotifFlat periodicStrip.width
      periodicStrip.period
      (Encodable.encode periodicStrip.motif)
      dimensionsValid periodicStrip.motif
  rw [Code.stripMotifProcess_encode] at loop
  simpa [stripWellFormedLoopCost,
    dimensionsValid, Code.stripMotifState] using
    comp loop
      (stripWellFormedLoopInput periodicStrip.width
        periodicStrip.period
        (Encodable.encode periodicStrip.motif))

def stripWellFormedHeaderCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  let result :=
    dimensionsValid &&
      motifInStripBounds periodicStrip.width
        periodicStrip.period periodicStrip.motif
  getCost 1
      (Code.stripMotifState periodicStrip.width
        periodicStrip.period result []) +
    stripWellFormedLoopCost periodicStrip

theorem stripWellFormedHeader
    (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) &&
        decide (0 < periodicStrip.period)
    EvaluatorCodeFits Code.stripWellFormedHeaderCode
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif]
      [(dimensionsValid &&
        motifInStripBounds periodicStrip.width
          periodicStrip.period
          periodicStrip.motif).toNat]
      (stripWellFormedHeaderCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  let result :=
    dimensionsValid &&
      motifInStripBounds periodicStrip.width
        periodicStrip.period periodicStrip.motif
  simpa [Code.stripWellFormedHeaderCode,
    stripWellFormedHeaderCost, dimensionsValid,
    result, Code.stripMotifState] using
    comp
      (get 1
        (Code.stripMotifState periodicStrip.width
          periodicStrip.period result []))
      (stripWellFormedLoop periodicStrip)

def stripWellFormedExplicitCost
    (periodicStrip : PeriodicStrip) : Nat :=
  stripWellFormedHeaderCost periodicStrip +
    periodicStripHeaderCost periodicStrip

theorem stripWellFormedExplicit
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.stripWellFormedExplicitCode
      [Encodable.encode periodicStrip]
      [periodicStrip.wellFormed.toNat]
      (stripWellFormedExplicitCost periodicStrip) := by
  have fitted :=
    comp
      (stripWellFormedHeader periodicStrip)
      (periodicStripHeader periodicStrip)
  simpa [Code.stripWellFormedExplicitCode,
    stripWellFormedExplicitCost,
    Code.stripWellFormedAccumulator_eq] using fitted

/-- Continuation-independent cost of the uniform-space certificate.  Unlike
`stripWellFormedExplicitCost`, its loop summand is reused rather than summed
over the numeric motif encoding. -/
def stripWellFormedUniformCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  let result :=
    dimensionsValid &&
      motifInStripBounds periodicStrip.width
        periodicStrip.period periodicStrip.motif
  getCost 1
      (Code.stripMotifState periodicStrip.width
        periodicStrip.period result []) +
    (stripMotifSpaceBound (Encodable.encode periodicStrip) +
      stripWellFormedLoopInputCost periodicStrip.width
        periodicStrip.period
        (Encodable.encode periodicStrip.motif)) +
    periodicStripHeaderCost periodicStrip

theorem stripWellFormedExplicitUniform
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.stripWellFormedExplicitCode
      [Encodable.encode periodicStrip]
      [periodicStrip.wellFormed.toNat]
      (stripWellFormedUniformCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  let result :=
    dimensionsValid &&
      motifInStripBounds periodicStrip.width
        periodicStrip.period periodicStrip.motif
  have loop :=
    stripMotifFlatUniform periodicStrip dimensionsValid
  have prepared :=
    comp loop
      (stripWellFormedLoopInput periodicStrip.width
        periodicStrip.period
        (Encodable.encode periodicStrip.motif))
  have projected :=
    comp
      (get 1
        (Code.stripMotifState periodicStrip.width
          periodicStrip.period result []))
      prepared
  have decoded :=
    comp projected (periodicStripHeader periodicStrip)
  simpa [Code.stripWellFormedExplicitCode,
    Code.stripWellFormedHeaderCode,
    stripWellFormedUniformCost, dimensionsValid, result,
    Code.stripMotifState,
    Code.stripWellFormedAccumulator_eq] using decoded

set_option maxHeartbeats 800000 in
theorem stripWellFormedLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip) :
    stripWellFormedLoopInputCost periodicStrip.width
        periodicStrip.period
        (Encodable.encode periodicStrip.motif) ≤
      10000000000000 *
        (encodedListSpace
          [Encodable.encode periodicStrip] + 1) := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  have widthBound :
      periodicStrip.width ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact Nat.left_le_pair _ _
  have periodBound :
      periodicStrip.period ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact (Nat.left_le_pair _ _).trans
      (Nat.right_le_pair _ _)
  have motifBound : motifCode ≤ stripCode := by
    simp only [motifCode, stripCode,
      PeriodicStrip.encode_eq_pair]
    exact (Nat.right_le_pair _ _).trans
      (Nat.right_le_pair _ _)
  have widthBits := encodeNat_length_mono widthBound
  have periodBits := encodeNat_length_mono periodBound
  have motifBits := encodeNat_length_mono motifBound
  have widthPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le periodicStrip.width).trans widthBound)
  have periodPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le periodicStrip.period).trans periodBound)
  have widthSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.width + 1 ≤ 8 * stripCode + 4
        by omega)
  have periodSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.period + 1 ≤ 8 * stripCode + 4
        by omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ 8 * stripCode + 4 by omega)
  have scaledBits :=
    encodeNat_eight_mul_add_four_length_le stripCode
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases widthEq : periodicStrip.width <;>
    cases periodEq : periodicStrip.period <;>
    simp [stripWellFormedLoopInputCost,
      stripWellFormedPayloadCost,
      stripWellFormedDimensionHeaderCost,
      stripDimensionsValidCost,
      stripDimensionWidthCost,
      stripDimensionPeriodCost, natPositiveCost,
      boolAndCost, normalizeBoolCost,
      branchZeroZeroCost, branchZeroSuccCost,
      branchZeroTestCost, prependCost, getCost,
      dropCost, headCost, idCost, nilCost,
      zeroCost, oneCost, tailCost, zeroPrimeCost,
      succCost, widthEq, periodEq,
      encodedListSpace_cons, encodedListSpace_nil,
      stripCode, motifCode, zeroBits, oneBits] at * <;>
    omega

set_option maxHeartbeats 800000 in
theorem stripWellFormedProjectionCost_le_linear
    (periodicStrip : PeriodicStrip) (result : Bool) :
    getCost 1
        (Code.stripMotifState periodicStrip.width
          periodicStrip.period result []) ≤
      1000000000000 *
        (encodedListSpace
          [Encodable.encode periodicStrip] + 1) := by
  let stripCode := Encodable.encode periodicStrip
  have widthBound :
      periodicStrip.width ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact Nat.left_le_pair _ _
  have periodBound :
      periodicStrip.period ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact (Nat.left_le_pair _ _).trans
      (Nat.right_le_pair _ _)
  have widthBits := encodeNat_length_mono widthBound
  have periodBits := encodeNat_length_mono periodBound
  have widthSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.width + 1 ≤ 8 * stripCode + 4
        by omega)
  have periodSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.period + 1 ≤ 8 * stripCode + 4
        by omega)
  have scaledBits :=
    encodeNat_eight_mul_add_four_length_le stripCode
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  cases result <;>
    simp [Code.stripMotifState, getCost, dropCost,
      headCost, idCost, nilCost, tailCost,
      zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      stripCode, zeroBits, oneBits, twoBits] at * <;>
    omega

def stripWellFormedInputSpaceBound
    (encodedStrip : Nat) : Nat :=
  1000000000000000 *
    (encodedListSpace [encodedStrip] + 1)

theorem stripWellFormedUniformCost_le_input
    (periodicStrip : PeriodicStrip) :
    stripWellFormedUniformCost periodicStrip ≤
      stripWellFormedInputSpaceBound
        (Encodable.encode periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) &&
      decide (0 < periodicStrip.period)
  let result :=
    dimensionsValid &&
      motifInStripBounds periodicStrip.width
        periodicStrip.period periodicStrip.motif
  have projection :=
    stripWellFormedProjectionCost_le_linear
      periodicStrip result
  have loopInput :=
    stripWellFormedLoopInputCost_le_linear periodicStrip
  have header :=
    periodicStripHeaderCost_le_linear periodicStrip
  simp only [result, dimensionsValid] at projection
  simp only [stripWellFormedUniformCost,
    stripWellFormedInputSpaceBound, stripMotifSpaceBound]
  omega

/-- The complete explicit well-formedness evaluator fits the same linear
allowance reserved for the other fixed strip arithmetic. -/
theorem stripWellFormedExplicitInputSpace
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.stripWellFormedExplicitCode
      [Encodable.encode periodicStrip]
      [periodicStrip.wellFormed.toNat]
      (stripWellFormedInputSpaceBound
        (Encodable.encode periodicStrip)) :=
  (stripWellFormedExplicitUniform periodicStrip).mono
    (stripWellFormedUniformCost_le_input periodicStrip)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
