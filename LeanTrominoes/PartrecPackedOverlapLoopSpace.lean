import LeanTrominoes.PartrecEncodedListDecodeSpace
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecPackedOverlapLoop
import LeanTrominoes.PartrecPackedOverlapAtSpace

/-!
# Evaluator-space certificates for packed overlap steps

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

def packedOverlapViewCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (remaining : List Cell) : Nat :=
  encodedListViewCost remaining +
    getCost 1
      (Code.packedOverlapState periodicStrip current next
        column valid remaining)

theorem packedOverlapView
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapViewCode
      (Code.packedOverlapState periodicStrip current next
        column valid remaining)
      (match remaining with
      | [] => [0, 0, 0]
      | cell :: suffix =>
          [1, Encodable.encode cell,
            Encodable.encode suffix])
      (packedOverlapViewCost
        periodicStrip current next column valid remaining) := by
  cases remaining with
  | nil =>
      simpa [Code.packedOverlapViewCode,
        packedOverlapViewCost] using
        comp (encodedListView ([] : List Cell))
          (get 1
            (Code.packedOverlapState periodicStrip current next
              column valid []))
  | cons cell remaining =>
      simpa [Code.packedOverlapViewCode,
        packedOverlapViewCost] using
        comp (encodedListView (cell :: remaining))
          (get 1
            (Code.packedOverlapState periodicStrip current next
              column valid (cell :: remaining)))

def packedOverlapHeadCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 1
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    packedOverlapViewCost periodicStrip current next column
      valid (cell :: remaining)

theorem packedOverlapHead
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapHeadCode
      (Code.packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      [Encodable.encode cell]
      (packedOverlapHeadCost
        periodicStrip current next column valid cell remaining) := by
  simpa [Code.packedOverlapHeadCode,
    packedOverlapHeadCost] using
    comp
      (get 1
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (packedOverlapView periodicStrip current next column
        valid (cell :: remaining))

def packedOverlapTailCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 2
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    packedOverlapViewCost periodicStrip current next column
      valid (cell :: remaining)

theorem packedOverlapTail
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapTailCode
      (Code.packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      [Encodable.encode remaining]
      (packedOverlapTailCost
        periodicStrip current next column valid cell remaining) := by
  simpa [Code.packedOverlapTailCode,
    packedOverlapTailCost] using
    comp
      (get 2
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (packedOverlapView periodicStrip current next column
        valid (cell :: remaining))

def packedOverlapAtArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  let rest4 :=
    prependCost state [current.assignmentWord]
      [next.assignmentWord]
      (getCost 4 state) (getCost 5 state)
  let restHead :=
    prependCost state [Encodable.encode cell]
      [current.assignmentWord, next.assignmentWord]
      (packedOverlapHeadCost
        periodicStrip current next column valid cell remaining)
      rest4
  let rest3 :=
    prependCost state [column.val]
      [Encodable.encode cell, current.assignmentWord,
        next.assignmentWord]
      (getCost 3 state) restHead
  let rest2 :=
    prependCost state [column.val + 1]
      [column.val, Encodable.encode cell,
        current.assignmentWord, next.assignmentWord]
      (getCost 2 state) rest3
  prependCost state [Encodable.encode periodicStrip.motif]
    [column.val + 1, column.val, Encodable.encode cell,
      current.assignmentWord, next.assignmentWord]
    (getCost 0 state) rest2

theorem packedOverlapAtArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapAtArgumentsCode
      (Code.packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      [Encodable.encode periodicStrip.motif,
        column.val + 1, column.val, Encodable.encode cell,
        current.assignmentWord, next.assignmentWord]
      (packedOverlapAtArgumentsCost
        periodicStrip current next column valid cell remaining) := by
  let state :=
    Code.packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  have rest4 := prepend (get 4 state) (get 5 state)
  have restHead :=
    prepend
      (packedOverlapHead periodicStrip current next column
        valid cell remaining)
      rest4
  have rest3 := prepend (get 3 state) restHead
  have rest2 := prepend (get 2 state) rest3
  have result := prepend (get 0 state) rest2
  simpa [Code.packedOverlapAtArgumentsCode,
    packedOverlapAtArgumentsCost,
    Code.packedOverlapState,
    prependCost, state] using result

def packedOverlapHeadValidCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  packedOverlapAtCost periodicStrip.motif
      (column.val + 1) column.val cell
      current.assignmentWord next.assignmentWord +
    packedOverlapAtArgumentsCost
      periodicStrip current next column valid cell remaining

theorem packedOverlapHeadValid
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapHeadValidCode
      (Code.packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      [(current.overlapsAtBool periodicStrip next column cell).toNat]
      (packedOverlapHeadValidCost
        periodicStrip current next column valid cell remaining) := by
  have fitted :=
    comp
      (packedOverlapAt periodicStrip.motif
        (column.val + 1) column.val cell
        current.assignmentWord next.assignmentWord)
      (packedOverlapAtArguments periodicStrip current next column
        valid cell remaining)
  have semantic :=
    Code.packedOverlapAtResult_eq_semantic
      periodicStrip current next column cell
  change
    (if
        (Code.packedAssignmentLookupOutcome periodicStrip.motif
            (column.val + 1) cell current.assignmentWord).2.1 =
          (Code.packedAssignmentLookupOutcome periodicStrip.motif
            column.val cell next.assignmentWord).2.1
      then 1 else 0) =
      (current.overlapsAtBool periodicStrip next column cell).toNat
    at semantic
  rw [semantic] at fitted
  simpa [Code.packedOverlapHeadValidCode,
    packedOverlapHeadValidCost] using fitted

def packedOverlapUpdatedValidCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  let cellTag :=
    (current.overlapsAtBool periodicStrip next column cell).toNat
  boolAndCost state valid.toNat cellTag
    (getCost 6 state)
    (packedOverlapHeadValidCost
      periodicStrip current next column valid cell remaining)

theorem packedOverlapUpdatedValid
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapUpdatedValidCode
      (Code.packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      [(valid &&
        current.overlapsAtBool periodicStrip next column cell).toNat]
      (packedOverlapUpdatedValidCost
        periodicStrip current next column valid cell remaining) := by
  have combined :=
    boolAnd
      (get 6
        (Code.packedOverlapState periodicStrip current next
          column valid (cell :: remaining)))
      (packedOverlapHeadValid periodicStrip current next column
        valid cell remaining)
  cases valid <;>
    cases overlap :
      current.overlapsAtBool periodicStrip next column cell <;>
    simpa [Code.packedOverlapUpdatedValidCode,
      packedOverlapUpdatedValidCost,
      Code.packedOverlapState, overlap] using combined

def packedOverlapConsStepCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  let nextValid :=
    valid &&
      current.overlapsAtBool periodicStrip next column cell
  let rest5 :=
    prependCost state [next.assignmentWord] [nextValid.toNat]
      (getCost 5 state)
      (packedOverlapUpdatedValidCost
        periodicStrip current next column valid cell remaining)
  let rest4 :=
    prependCost state [current.assignmentWord]
      [next.assignmentWord, nextValid.toNat]
      (getCost 4 state) rest5
  let rest3 :=
    prependCost state [column.val]
      [current.assignmentWord, next.assignmentWord,
        nextValid.toNat]
      (getCost 3 state) rest4
  let rest2 :=
    prependCost state [column.val + 1]
      [column.val, current.assignmentWord,
        next.assignmentWord, nextValid.toNat]
      (getCost 2 state) rest3
  let rest1 :=
    prependCost state [Encodable.encode remaining]
      [column.val + 1, column.val, current.assignmentWord,
        next.assignmentWord, nextValid.toNat]
      (packedOverlapTailCost
        periodicStrip current next column valid cell remaining)
      rest2
  prependCost state [Encodable.encode periodicStrip.motif]
    [Encodable.encode remaining, column.val + 1,
      column.val, current.assignmentWord,
      next.assignmentWord, nextValid.toNat]
    (getCost 0 state) rest1

theorem packedOverlapConsStep
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    let nextValid :=
      valid &&
        current.overlapsAtBool periodicStrip next column cell
    EvaluatorCodeFits Code.packedOverlapConsStepCode
      (Code.packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      (Code.packedOverlapState periodicStrip current next
        column nextValid remaining)
      (packedOverlapConsStepCost
        periodicStrip current next column valid cell remaining) := by
  let state :=
    Code.packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  have rest5 :=
    prepend (get 5 state)
      (packedOverlapUpdatedValid periodicStrip current next column
        valid cell remaining)
  have rest4 := prepend (get 4 state) rest5
  have rest3 := prepend (get 3 state) rest4
  have rest2 := prepend (get 2 state) rest3
  have rest1 :=
    prepend
      (packedOverlapTail periodicStrip current next column
        valid cell remaining)
      rest2
  have result := prepend (get 0 state) rest1
  simpa [Code.packedOverlapConsStepCode,
    packedOverlapConsStepCost,
    Code.packedOverlapState,
    prependCost, state] using result

def packedOverlapStepCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) : List Cell → Nat
  | [] =>
      let state :=
        Code.packedOverlapState periodicStrip current next
          column valid []
      branchZeroZeroCost state state 0
        (getCost 1 state) (idCost state)
  | cell :: remaining =>
      let state :=
        Code.packedOverlapState periodicStrip current next
          column valid (cell :: remaining)
      let nextValid :=
        valid &&
          current.overlapsAtBool periodicStrip next column cell
      branchZeroSuccCost state
        (Code.packedOverlapState periodicStrip current next
          column nextValid remaining)
        (Encodable.encode (cell :: remaining))
        (getCost 1 state)
        (packedOverlapConsStepCost periodicStrip current next
          column valid cell remaining)

theorem packedOverlapStep
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedOverlapStepCode
      (Code.packedOverlapState periodicStrip current next
        column valid remaining)
      (Code.packedOverlapNativeStep
        periodicStrip current next column
        (Code.packedOverlapState periodicStrip current next
          column valid remaining))
      (packedOverlapStepCost
        periodicStrip current next column valid remaining) := by
  cases remaining with
  | nil =>
      simpa [Code.packedOverlapStepCode,
        packedOverlapStepCost] using
        branchZero_zero rfl
          (get 1
            (Code.packedOverlapState periodicStrip current next
              column valid []))
          (id
            (Code.packedOverlapState periodicStrip current next
              column valid []))
  | cons cell remaining =>
      have positive :
          0 < Encodable.encode (cell :: remaining) := by
        simp
      simpa [Code.packedOverlapStepCode,
        packedOverlapStepCost] using
        branchZero_succ positive
          (get 1
            (Code.packedOverlapState periodicStrip current next
              column valid (cell :: remaining)))
          (packedOverlapConsStep periodicStrip current next column
            valid cell remaining)

def packedOverlapBodyCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) : Nat :=
  flatCountdownBodyCost
    (Code.packedOverlapNativeStep
      periodicStrip current next column)
    (fun _ =>
      packedOverlapStepCost periodicStrip current next
        column valid remaining)
    countdown
    (Code.packedOverlapState periodicStrip current next
      column valid remaining)

theorem packedOverlapBody
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody
        Code.packedOverlapStepCode)
      (countdown ::
        Code.packedOverlapState periodicStrip current next
          column valid remaining)
      (flatCountdownOutput
        (Code.packedOverlapNativeStep
          periodicStrip current next column)
        countdown
        (Code.packedOverlapState periodicStrip current next
          column valid remaining))
      (packedOverlapBodyCost periodicStrip current next column
        countdown valid remaining) := by
  cases countdown with
  | zero =>
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, packedOverlapBodyCost,
        flatCountdownBodyCost, zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one
              (.cons Code.head
                (Code.packedOverlapStepCode.comp
                  Code.tail)))
          (values :=
            0 ::
              Code.packedOverlapState periodicStrip current next
                column valid remaining)
          (by rfl)
          (zero'_named
            (Code.packedOverlapState periodicStrip current next
              column valid remaining))
  | succ countdown =>
      let payload :=
        Code.packedOverlapState periodicStrip current next
          column valid remaining
      let values := countdown :: payload
      have transformed :=
        comp
          (packedOverlapStep periodicStrip current next column
            valid remaining)
          (tail_named values)
      have payloadResult :=
        prepend (head values) transformed
      have branch :=
        prepend (one values) payloadResult
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, packedOverlapBodyCost,
        flatCountdownBodyCost,
        flatCountdownSuccBranchCost,
        payload, values, prependCost,
        Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values := (countdown + 1) :: payload)
          (predecessor := countdown)
          (by rfl) branch

set_option maxHeartbeats 800000 in
theorem packedOverlapBodyCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) :
    packedOverlapBodyCost periodicStrip current next column
        countdown valid remaining ≤
      1000000000000000000000000000000000 *
        (encodedListSpace
          [4096 * (countdown +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode remaining +
            Encodable.encode remaining +
            Encodable.encode remaining +
            column.val + current.assignmentWord +
            next.assignmentWord + 100) + 2000] +
          1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let remainingCode := Encodable.encode remaining
  let limit :=
    4096 * (countdown +
      motifCode + motifCode + motifCode +
      remainingCode + remainingCode + remainingCode +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  change
    packedOverlapBodyCost periodicStrip current next column
        countdown valid remaining ≤
      1000000000000000000000000000000000 *
        (encodedListSpace [limit] + 1)
  have countdownBound : countdown ≤ limit := by
    simp only [limit]
    omega
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have remainingBound : remainingCode ≤ limit := by
    simp only [limit]
    omega
  have columnBound : column.val ≤ limit := by
    simp only [limit]
    omega
  have wordBound : current.assignmentWord ≤ limit := by
    simp only [limit]
    omega
  have nextWordBound : next.assignmentWord ≤ limit := by
    simp only [limit]
    omega
  have countdownBits := encodeNat_length_mono countdownBound
  have countdownPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le countdown).trans countdownBound)
  have motifBits := encodeNat_length_mono motifBound
  have remainingBits := encodeNat_length_mono remainingBound
  have columnBits := encodeNat_length_mono columnBound
  have wordBits := encodeNat_length_mono wordBound
  have nextWordBits := encodeNat_length_mono nextWordBound
  have countdownSuccBits :=
    encodeNat_length_mono
      (show countdown + 1 ≤ limit by
        simp only [limit]
        omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have remainingSuccBits :=
    encodeNat_length_mono
      (show remainingCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have columnSuccBits :=
    encodeNat_length_mono
      (show column.val + 1 ≤ limit by
        simp only [limit]
        omega)
  have columnTwoSuccBits :=
    encodeNat_length_mono
      (show column.val + 1 + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show current.assignmentWord + 1 ≤ limit by
        simp only [limit]
        omega)
  have nextWordSuccBits :=
    encodeNat_length_mono
      (show next.assignmentWord + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have oneLimitBits :=
    encodeNat_length_mono
      (show 1 ≤ limit by
        simp only [limit]
        omega)
  have positiveLimitBits :
      1 ≤ (Computability.encodeNat limit).length := by
    simpa [oneBits] using oneLimitBits
  have validBits :
      (Computability.encodeNat valid.toNat).length ≤
        (Computability.encodeNat limit).length := by
    cases valid
    · simp [zeroBits]
    · simpa [oneBits] using positiveLimitBits
  cases remaining with
  | nil =>
      have nextStateSpace :
          encodedListSpace
              (Code.packedOverlapNativeStep periodicStrip current next
                column
                (Code.packedOverlapState periodicStrip current next
                  column valid [])) ≤
            10 * ((Computability.encodeNat limit).length + 2) := by
        rw [Code.packedOverlapNativeStep_state_nil]
        cases valid <;>
          simp [Code.packedOverlapState,
            encodedListSpace_cons, encodedListSpace_nil,
            motifCode, zeroBits, oneBits] at * <;>
          omega
      cases countdown <;>
        cases valid <;>
        simp [packedOverlapBodyCost,
          packedOverlapStepCost,
          flatCountdownBodyCost,
          flatCountdownSuccBranchCost,
          branchZeroZeroCost, branchZeroTestCost,
          prependCost, getCost, dropCost, idCost,
          headCost, nilCost, oneCost, zeroCost,
          zeroPrimeCost, tailCost, succCost,
          Code.packedOverlapState,
          encodedListSpace_cons, encodedListSpace_nil,
          motifCode, remainingCode, limit,
          zeroBits, oneBits, twoBits] at * <;>
        clear * - countdownBits countdownPredBits
          motifBits remainingBits
          columnBits wordBits nextWordBits countdownSuccBits
          motifSuccBits
          remainingSuccBits columnSuccBits wordSuccBits
          columnTwoSuccBits nextWordSuccBits
          nextStateSpace <;>
        omega
  | cons cell remaining =>
      let cellCode := Encodable.encode cell
      let tailCode := Encodable.encode remaining
      have cellRemaining :
          cellCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons, cellCode]
        exact
          (Nat.left_le_pair cellCode tailCode).trans
            (Nat.le_succ _)
      have tailRemaining :
          tailCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons, tailCode]
        exact
          (Nat.right_le_pair cellCode tailCode).trans
            (Nat.le_succ _)
      have cellLimit : cellCode ≤ limit :=
        cellRemaining.trans (by
          simpa [remainingCode] using remainingBound)
      have tailLimit : tailCode ≤ limit :=
        tailRemaining.trans (by
          simpa [remainingCode] using remainingBound)
      have cellBits := encodeNat_length_mono cellLimit
      have tailBits := encodeNat_length_mono tailLimit
      have constructorBits :=
        encodeNat_length_mono
          (show Nat.pair cellCode tailCode ≤ limit by
            exact (Nat.le_succ _).trans
              (by simpa [remainingCode] using remainingBound))
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
      have viewBound :=
        encodedListViewCost_le_linear (cell :: remaining)
      have viewLimit :
          encodedListSpace
              [2 * Encodable.encode (cell :: remaining) + 4] ≤
            encodedListSpace [limit] := by
        have numeric :
            2 * Encodable.encode (cell :: remaining) + 4 ≤
              limit := by
          simp only [limit]
          omega
        simpa only [encodedListSpace_cons,
          encodedListSpace_nil, Nat.add_le_add_iff_right] using
          encodeNat_length_mono numeric
      have viewGlobal :
          encodedListViewCost (cell :: remaining) ≤
            2000000000 *
              (encodedListSpace [limit] + 1) := by
        exact viewBound.trans
          (Nat.mul_le_mul_left 2000000000
            (Nat.add_le_add_right viewLimit 1))
      let overlapLimit :=
        64 * (motifCode + motifCode + motifCode +
          cellCode + (column.val + 1) + current.assignmentWord +
          motifCode + motifCode + motifCode +
          cellCode + column.val + next.assignmentWord + 100) +
          1000
      have overlapNumeric : overlapLimit ≤ limit := by
        simp only [overlapLimit, limit]
        omega
      have overlapBits :=
        encodeNat_length_mono overlapNumeric
      have overlapLocal :=
        packedOverlapAtCost_le_linear periodicStrip.motif
          (column.val + 1) column.val cell
          current.assignmentWord next.assignmentWord
      have overlapGlobal :
          packedOverlapAtCost periodicStrip.motif
              (column.val + 1) column.val cell
              current.assignmentWord next.assignmentWord ≤
            100000000000000000000000 *
              (encodedListSpace [limit] + 1) := by
        have aligned :
            packedOverlapAtCost periodicStrip.motif
                (column.val + 1) column.val cell
                current.assignmentWord next.assignmentWord ≤
              100000000000000000000000 *
                (encodedListSpace [overlapLimit] + 1) := by
          simpa [packedOverlapAtSpaceBound,
            overlapLimit, motifCode, cellCode] using
            overlapLocal
        simp only [encodedListSpace_cons,
          encodedListSpace_nil] at aligned ⊢
        omega
      have tailBitsRaw :
          (Computability.encodeNat
            (Encodable.encode remaining)).length ≤
              (Computability.encodeNat limit).length := by
        simpa [tailCode] using tailBits
      have motifBitsRaw :
          (Computability.encodeNat
            (Encodable.encode periodicStrip.motif)).length ≤
              (Computability.encodeNat limit).length := by
        simpa [motifCode] using motifBits
      have nextStateFieldBits :
          (Computability.encodeNat
                (Encodable.encode periodicStrip.motif)).length +
              (Computability.encodeNat
                (Encodable.encode remaining)).length +
              (Computability.encodeNat (column.val + 1)).length +
              (Computability.encodeNat column.val).length +
              (Computability.encodeNat
                current.assignmentWord).length +
              (Computability.encodeNat
                next.assignmentWord).length ≤
            6 * (Computability.encodeNat limit).length := by
        clear * - motifBitsRaw tailBitsRaw columnSuccBits
          columnBits wordBits nextWordBits
        omega
      have nextStateSpace :
          encodedListSpace
              (Code.packedOverlapNativeStep periodicStrip current next
                column
                (Code.packedOverlapState periodicStrip current next
                  column valid (cell :: remaining))) ≤
            10 * ((Computability.encodeNat limit).length + 2) := by
        rw [Code.packedOverlapNativeStep_state_cons]
        cases valid <;>
          cases overlap :
            current.overlapsAtBool periodicStrip next column cell <;>
          simp [Code.packedOverlapState,
            encodedListSpace_cons, encodedListSpace_nil,
            zeroBits, oneBits] <;>
          clear * - nextStateFieldBits <;>
          omega
      cases countdown with
      | zero =>
          cases valid <;>
            simp [packedOverlapBodyCost,
              flatCountdownBodyCost, zeroPrimeCost,
              Code.packedOverlapState,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, remainingCode, cellCode, tailCode,
              limit, zeroBits, oneBits, twoBits] at * <;>
            clear * - countdownBits countdownPredBits
              motifBits remainingBits
              columnBits wordBits nextWordBits countdownSuccBits
              motifSuccBits
              remainingSuccBits columnSuccBits wordSuccBits
              columnTwoSuccBits nextWordSuccBits
              cellBits tailBits constructorBits cellSuccBits
              tailSuccBits nextStateSpace <;>
            omega
      | succ countdown =>
          cases valid <;>
            cases overlap :
              current.overlapsAtBool periodicStrip next column cell <;>
            simp [packedOverlapBodyCost,
              packedOverlapStepCost,
              packedOverlapConsStepCost,
              packedOverlapUpdatedValidCost,
              packedOverlapHeadValidCost,
              packedOverlapAtArgumentsCost,
              packedOverlapHeadCost,
              packedOverlapTailCost,
              packedOverlapViewCost,
              flatCountdownBodyCost,
              flatCountdownSuccBranchCost,
              branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, boolAndCost,
              normalizeBoolCost, prependCost,
              getCost, dropCost, idCost, headCost,
              nilCost, oneCost, zeroCost, zeroPrimeCost,
              tailCost, succCost,
              Code.packedOverlapState,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, remainingCode, cellCode, tailCode,
              limit, overlap,
              zeroBits, oneBits, twoBits] at * <;>
            clear * - countdownBits countdownPredBits
              motifBits remainingBits
              columnBits wordBits nextWordBits countdownSuccBits
              motifSuccBits
              remainingSuccBits columnSuccBits wordSuccBits
              columnTwoSuccBits nextWordSuccBits
              cellBits tailBits constructorBits cellSuccBits
              tailSuccBits viewGlobal overlapGlobal
              nextStateSpace <;>
            omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
