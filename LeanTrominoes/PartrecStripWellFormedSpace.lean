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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
