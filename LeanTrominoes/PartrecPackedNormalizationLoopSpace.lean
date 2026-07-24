import LeanTrominoes.PartrecEncodedListDecodeSpace
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecPackedNormalizationLoop
import LeanTrominoes.PartrecPackedNormalizedAtSpace

/-!
# Evaluator-space certificates for packed normalization steps

This module fits every component of one streaming motif step and the
surrounding flat-countdown body.  A later uniform theorem will reuse these
exact certificates under the reachable encoded-suffix invariant.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def packedNormalizationViewCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (remaining : List Cell) : Nat :=
  encodedListViewCost remaining +
    getCost 1
      (Code.packedNormalizationState periodicStrip packed
        column valid remaining)

theorem packedNormalizationView
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationViewCode
      (Code.packedNormalizationState periodicStrip packed
        column valid remaining)
      (match remaining with
      | [] => [0, 0, 0]
      | cell :: suffix =>
          [1, Encodable.encode cell,
            Encodable.encode suffix])
      (packedNormalizationViewCost
        periodicStrip packed column valid remaining) := by
  cases remaining with
  | nil =>
      simpa [Code.packedNormalizationViewCode,
        packedNormalizationViewCost] using
        comp (encodedListView ([] : List Cell))
          (get 1
            (Code.packedNormalizationState periodicStrip packed
              column valid []))
  | cons cell remaining =>
      simpa [Code.packedNormalizationViewCode,
        packedNormalizationViewCost] using
        comp (encodedListView (cell :: remaining))
          (get 1
            (Code.packedNormalizationState periodicStrip packed
              column valid (cell :: remaining)))

def packedNormalizationHeadCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 1
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    packedNormalizationViewCost periodicStrip packed column
      valid (cell :: remaining)

theorem packedNormalizationHead
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationHeadCode
      (Code.packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      [Encodable.encode cell]
      (packedNormalizationHeadCost
        periodicStrip packed column valid cell remaining) := by
  simpa [Code.packedNormalizationHeadCode,
    packedNormalizationHeadCost] using
    comp
      (get 1
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (packedNormalizationView periodicStrip packed column
        valid (cell :: remaining))

def packedNormalizationTailCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 2
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    packedNormalizationViewCost periodicStrip packed column
      valid (cell :: remaining)

theorem packedNormalizationTail
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationTailCode
      (Code.packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      [Encodable.encode remaining]
      (packedNormalizationTailCost
        periodicStrip packed column valid cell remaining) := by
  simpa [Code.packedNormalizationTailCode,
    packedNormalizationTailCost] using
    comp
      (get 2
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (packedNormalizationView periodicStrip packed column
        valid (cell :: remaining))

def packedNormalizationAtArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  let rest5 :=
    prependCost state [Encodable.encode cell]
      [packed.assignmentWord]
      (packedNormalizationHeadCost
        periodicStrip packed column valid cell remaining)
      (getCost 5 state)
  let rest4 :=
    prependCost state [column.val]
      [Encodable.encode cell, packed.assignmentWord]
      (getCost 4 state) rest5
  let rest0 :=
    prependCost state [Encodable.encode periodicStrip.motif]
      [column.val, Encodable.encode cell,
        packed.assignmentWord]
      (getCost 0 state) rest4
  let rest3 :=
    prependCost state [packed.phase]
      [Encodable.encode periodicStrip.motif,
        column.val, Encodable.encode cell,
        packed.assignmentWord]
      (getCost 3 state) rest0
  prependCost state [periodicStrip.period]
    [packed.phase, Encodable.encode periodicStrip.motif,
      column.val, Encodable.encode cell,
      packed.assignmentWord]
    (getCost 2 state) rest3

theorem packedNormalizationAtArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationAtArgumentsCode
      (Code.packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif, column.val,
        Encodable.encode cell, packed.assignmentWord]
      (packedNormalizationAtArgumentsCost
        periodicStrip packed column valid cell remaining) := by
  let state :=
    Code.packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  have rest5 :=
    prepend
      (packedNormalizationHead periodicStrip packed column
        valid cell remaining)
      (get 5 state)
  have rest4 := prepend (get 4 state) rest5
  have rest0 := prepend (get 0 state) rest4
  have rest3 := prepend (get 3 state) rest0
  have result := prepend (get 2 state) rest3
  simpa [Code.packedNormalizationAtArgumentsCode,
    packedNormalizationAtArgumentsCost,
    Code.packedNormalizationState,
    prependCost, state] using result

def packedNormalizationHeadValidCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  packedNormalizedAtCost periodicStrip.period packed.phase
      periodicStrip.motif column.val cell packed.assignmentWord +
    packedNormalizationAtArgumentsCost
      periodicStrip packed column valid cell remaining

theorem packedNormalizationHeadValid
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationHeadValidCode
      (Code.packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      [(packed.normalizedAtBool periodicStrip column cell).toNat]
      (packedNormalizationHeadValidCost
        periodicStrip packed column valid cell remaining) := by
  have fitted :=
    comp
      (packedNormalizedAtResult periodicStrip.period packed.phase
        periodicStrip.motif column.val cell packed.assignmentWord)
      (packedNormalizationAtArguments periodicStrip packed column
        valid cell remaining)
  rw [Code.packedNormalizedAtResult_eq_semantic] at fitted
  simpa [Code.packedNormalizationHeadValidCode,
    packedNormalizationHeadValidCost] using fitted

def packedNormalizationUpdatedValidCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  let cellTag :=
    (packed.normalizedAtBool periodicStrip column cell).toNat
  boolAndCost state valid.toNat cellTag
    (getCost 6 state)
    (packedNormalizationHeadValidCost
      periodicStrip packed column valid cell remaining)

theorem packedNormalizationUpdatedValid
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationUpdatedValidCode
      (Code.packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      [(valid &&
        packed.normalizedAtBool periodicStrip column cell).toNat]
      (packedNormalizationUpdatedValidCost
        periodicStrip packed column valid cell remaining) := by
  have combined :=
    boolAnd
      (get 6
        (Code.packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)))
      (packedNormalizationHeadValid periodicStrip packed column
        valid cell remaining)
  cases valid <;>
    cases normalized :
      packed.normalizedAtBool periodicStrip column cell <;>
    simpa [Code.packedNormalizationUpdatedValidCode,
      packedNormalizationUpdatedValidCost,
      Code.packedNormalizationState, normalized] using combined

def packedNormalizationConsStepCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  let nextValid :=
    valid &&
      packed.normalizedAtBool periodicStrip column cell
  let rest5 :=
    prependCost state [packed.assignmentWord] [nextValid.toNat]
      (getCost 5 state)
      (packedNormalizationUpdatedValidCost
        periodicStrip packed column valid cell remaining)
  let rest4 :=
    prependCost state [column.val]
      [packed.assignmentWord, nextValid.toNat]
      (getCost 4 state) rest5
  let rest3 :=
    prependCost state [packed.phase]
      [column.val, packed.assignmentWord, nextValid.toNat]
      (getCost 3 state) rest4
  let rest2 :=
    prependCost state [periodicStrip.period]
      [packed.phase, column.val, packed.assignmentWord,
        nextValid.toNat]
      (getCost 2 state) rest3
  let rest1 :=
    prependCost state [Encodable.encode remaining]
      [periodicStrip.period, packed.phase, column.val,
        packed.assignmentWord, nextValid.toNat]
      (packedNormalizationTailCost
        periodicStrip packed column valid cell remaining)
      rest2
  prependCost state [Encodable.encode periodicStrip.motif]
    [Encodable.encode remaining, periodicStrip.period,
      packed.phase, column.val, packed.assignmentWord,
      nextValid.toNat]
    (getCost 0 state) rest1

theorem packedNormalizationConsStep
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    let nextValid :=
      valid &&
        packed.normalizedAtBool periodicStrip column cell
    EvaluatorCodeFits Code.packedNormalizationConsStepCode
      (Code.packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      (Code.packedNormalizationState periodicStrip packed
        column nextValid remaining)
      (packedNormalizationConsStepCost
        periodicStrip packed column valid cell remaining) := by
  let state :=
    Code.packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  have rest5 :=
    prepend (get 5 state)
      (packedNormalizationUpdatedValid periodicStrip packed column
        valid cell remaining)
  have rest4 := prepend (get 4 state) rest5
  have rest3 := prepend (get 3 state) rest4
  have rest2 := prepend (get 2 state) rest3
  have rest1 :=
    prepend
      (packedNormalizationTail periodicStrip packed column
        valid cell remaining)
      rest2
  have result := prepend (get 0 state) rest1
  simpa [Code.packedNormalizationConsStepCode,
    packedNormalizationConsStepCost,
    Code.packedNormalizationState,
    prependCost, state] using result

def packedNormalizationStepCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) : List Cell → Nat
  | [] =>
      let state :=
        Code.packedNormalizationState periodicStrip packed
          column valid []
      branchZeroZeroCost state state 0
        (getCost 1 state) (idCost state)
  | cell :: remaining =>
      let state :=
        Code.packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)
      let nextValid :=
        valid &&
          packed.normalizedAtBool periodicStrip column cell
      branchZeroSuccCost state
        (Code.packedNormalizationState periodicStrip packed
          column nextValid remaining)
        (Encodable.encode (cell :: remaining))
        (getCost 1 state)
        (packedNormalizationConsStepCost periodicStrip packed
          column valid cell remaining)

theorem packedNormalizationStep
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedNormalizationStepCode
      (Code.packedNormalizationState periodicStrip packed
        column valid remaining)
      (Code.packedNormalizationNativeStep
        periodicStrip packed column
        (Code.packedNormalizationState periodicStrip packed
          column valid remaining))
      (packedNormalizationStepCost
        periodicStrip packed column valid remaining) := by
  cases remaining with
  | nil =>
      simpa [Code.packedNormalizationStepCode,
        packedNormalizationStepCost] using
        branchZero_zero rfl
          (get 1
            (Code.packedNormalizationState periodicStrip packed
              column valid []))
          (id
            (Code.packedNormalizationState periodicStrip packed
              column valid []))
  | cons cell remaining =>
      have positive :
          0 < Encodable.encode (cell :: remaining) := by
        simp
      simpa [Code.packedNormalizationStepCode,
        packedNormalizationStepCost] using
        branchZero_succ positive
          (get 1
            (Code.packedNormalizationState periodicStrip packed
              column valid (cell :: remaining)))
          (packedNormalizationConsStep periodicStrip packed column
            valid cell remaining)

def packedNormalizationBodyCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) : Nat :=
  flatCountdownBodyCost
    (Code.packedNormalizationNativeStep
      periodicStrip packed column)
    (fun _ =>
      packedNormalizationStepCost periodicStrip packed
        column valid remaining)
    countdown
    (Code.packedNormalizationState periodicStrip packed
      column valid remaining)

theorem packedNormalizationBody
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody
        Code.packedNormalizationStepCode)
      (countdown ::
        Code.packedNormalizationState periodicStrip packed
          column valid remaining)
      (flatCountdownOutput
        (Code.packedNormalizationNativeStep
          periodicStrip packed column)
        countdown
        (Code.packedNormalizationState periodicStrip packed
          column valid remaining))
      (packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining) := by
  cases countdown with
  | zero =>
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, packedNormalizationBodyCost,
        flatCountdownBodyCost, zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one
              (.cons Code.head
                (Code.packedNormalizationStepCode.comp
                  Code.tail)))
          (values :=
            0 ::
              Code.packedNormalizationState periodicStrip packed
                column valid remaining)
          (by rfl)
          (zero'_named
            (Code.packedNormalizationState periodicStrip packed
              column valid remaining))
  | succ countdown =>
      let payload :=
        Code.packedNormalizationState periodicStrip packed
          column valid remaining
      let values := countdown :: payload
      have transformed :=
        comp
          (packedNormalizationStep periodicStrip packed column
            valid remaining)
          (tail_named values)
      have payloadResult :=
        prepend (head values) transformed
      have branch :=
        prepend (one values) payloadResult
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, packedNormalizationBodyCost,
        flatCountdownBodyCost,
        flatCountdownSuccBranchCost,
        payload, values, prependCost,
        Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values := (countdown + 1) :: payload)
          (predecessor := countdown)
          (by rfl) branch

def packedNormalizationLoopInputCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      column.val, packed.assignmentWord]
  let rest7 :=
    prependCost values [packed.assignmentWord] [1]
      (getCost 4 values) (oneCost values)
  let rest6 :=
    prependCost values [column.val]
      [packed.assignmentWord, 1]
      (getCost 3 values) rest7
  let rest5 :=
    prependCost values [packed.phase]
      [column.val, packed.assignmentWord, 1]
      (getCost 1 values) rest6
  let rest4 :=
    prependCost values [periodicStrip.period]
      [packed.phase, column.val, packed.assignmentWord, 1]
      (getCost 0 values) rest5
  let rest3 :=
    prependCost values [Encodable.encode periodicStrip.motif]
      [periodicStrip.period, packed.phase, column.val,
        packed.assignmentWord, 1]
      (getCost 2 values) rest4
  let rest2 :=
    prependCost values [Encodable.encode periodicStrip.motif]
      [Encodable.encode periodicStrip.motif,
        periodicStrip.period, packed.phase, column.val,
        packed.assignmentWord, 1]
      (getCost 2 values) rest3
  prependCost values [Encodable.encode periodicStrip.motif]
    [Encodable.encode periodicStrip.motif,
      Encodable.encode periodicStrip.motif,
      periodicStrip.period, packed.phase, column.val,
      packed.assignmentWord, 1]
    (getCost 2 values) rest2

theorem packedNormalizationLoopInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    EvaluatorCodeFits Code.packedNormalizationLoopInputCode
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        column.val, packed.assignmentWord]
      (Encodable.encode periodicStrip.motif ::
        Code.packedNormalizationState periodicStrip packed
          column true periodicStrip.motif)
      (packedNormalizationLoopInputCost
        periodicStrip packed column) := by
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      column.val, packed.assignmentWord]
  have rest7 := prepend (get 4 values) (one values)
  have rest6 := prepend (get 3 values) rest7
  have rest5 := prepend (get 1 values) rest6
  have rest4 := prepend (get 0 values) rest5
  have rest3 := prepend (get 2 values) rest4
  have rest2 := prepend (get 2 values) rest3
  have result := prepend (get 2 values) rest2
  simpa [Code.packedNormalizationLoopInputCode,
    packedNormalizationLoopInputCost,
    Code.packedNormalizationState,
    prependCost, values] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
