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

def packedOverlapLoopInputCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) : Nat :=
  let values :=
    [Encodable.encode periodicStrip.motif,
      column.val + 1, column.val,
      current.assignmentWord, next.assignmentWord]
  let rest7 :=
    prependCost values [next.assignmentWord] [1]
      (getCost 4 values) (oneCost values)
  let rest6 :=
    prependCost values [current.assignmentWord]
      [next.assignmentWord, 1]
      (getCost 3 values) rest7
  let rest5 :=
    prependCost values [column.val]
      [current.assignmentWord, next.assignmentWord, 1]
      (getCost 2 values) rest6
  let rest4 :=
    prependCost values [column.val + 1]
      [column.val, current.assignmentWord,
        next.assignmentWord, 1]
      (getCost 1 values) rest5
  let rest3 :=
    prependCost values [Encodable.encode periodicStrip.motif]
      [column.val + 1, column.val, current.assignmentWord,
        next.assignmentWord, 1]
      (getCost 0 values) rest4
  let rest2 :=
    prependCost values [Encodable.encode periodicStrip.motif]
      [Encodable.encode periodicStrip.motif,
        column.val + 1, column.val, current.assignmentWord,
        next.assignmentWord, 1]
      (getCost 0 values) rest3
  prependCost values [Encodable.encode periodicStrip.motif]
    [Encodable.encode periodicStrip.motif,
      Encodable.encode periodicStrip.motif,
      column.val + 1, column.val, current.assignmentWord,
      next.assignmentWord, 1]
    (getCost 0 values) rest2

theorem packedOverlapLoopInput
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    EvaluatorCodeFits Code.packedOverlapLoopInputCode
      [Encodable.encode periodicStrip.motif,
        column.val + 1, column.val,
        current.assignmentWord, next.assignmentWord]
      (Encodable.encode periodicStrip.motif ::
        Code.packedOverlapState periodicStrip current next
          column true periodicStrip.motif)
      (packedOverlapLoopInputCost
        periodicStrip current next column) := by
  let values :=
    [Encodable.encode periodicStrip.motif,
      column.val + 1, column.val,
      current.assignmentWord, next.assignmentWord]
  have rest7 := prepend (get 4 values) (one values)
  have rest6 := prepend (get 3 values) rest7
  have rest5 := prepend (get 2 values) rest6
  have rest4 := prepend (get 1 values) rest5
  have rest3 := prepend (get 0 values) rest4
  have rest2 := prepend (get 0 values) rest3
  have result := prepend (get 0 values) rest2
  simpa [Code.packedOverlapLoopInputCode,
    packedOverlapLoopInputCost,
    Code.packedOverlapState,
    prependCost, values] using result

def packedOverlapPolynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) : Nat :=
  1000000000000000000000000000000000 *
    (encodedListSpace
      [4096 * (
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        column.val + current.assignmentWord +
        next.assignmentWord + 100) + 2000] + 1)

theorem packedOverlapBodyCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (countdown : Nat) (valid : Bool)
    (remaining leading : List Cell)
    (countdownBound :
      countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedOverlapBodyCost periodicStrip current next column
        countdown valid remaining ≤
      packedOverlapPolynomialSpaceBound
        periodicStrip current next column := by
  let motifCode := Encodable.encode periodicStrip.motif
  let remainingCode := Encodable.encode remaining
  let localLimit :=
    4096 * (countdown +
      motifCode + motifCode + motifCode +
      remainingCode + remainingCode + remainingCode +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  let globalLimit :=
    4096 * (motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode + motifCode +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  have remainingBound : remainingCode ≤ motifCode := by
    simp only [remainingCode, motifCode]
    rw [suffix]
    exact encode_list_suffix_le leading remaining
  have numeric : localLimit ≤ globalLimit := by
    simp only [localLimit, globalLimit]
    omega
  have bits := encodeNat_length_mono numeric
  have body :=
    packedOverlapBodyCost_le_linear periodicStrip current next
      column countdown valid remaining
  have bodyLocal :
      packedOverlapBodyCost periodicStrip current next column
          countdown valid remaining ≤
        1000000000000000000000000000000000 *
          (encodedListSpace [localLimit] + 1) := by
    simpa [localLimit, motifCode, remainingCode] using body
  simp only [packedOverlapPolynomialSpaceBound,
    encodedListSpace_cons, encodedListSpace_nil]
  change
    packedOverlapBodyCost periodicStrip current next column
        countdown valid remaining ≤
      1000000000000000000000000000000000 *
        ((Computability.encodeNat globalLimit).length + 1 + 1)
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at bodyLocal
  exact bodyLocal.trans
    (Nat.mul_le_mul_left
      1000000000000000000000000000000000
      (by omega))

/-- Typed motif-suffix states reachable while one overlap countdown runs. -/
def PackedOverlapReachable
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (countdown : Nat) (values : List Nat) : Prop :=
  ∃ valid remaining leading,
    values =
      Code.packedOverlapState periodicStrip current next
        column valid remaining ∧
    countdown ≤ Encodable.encode periodicStrip.motif ∧
    periodicStrip.motif = leading ++ remaining

theorem packedOverlapReachable_initial
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) :
    PackedOverlapReachable periodicStrip current next column
      (Encodable.encode periodicStrip.motif)
      (Code.packedOverlapState periodicStrip current next
        column valid periodicStrip.motif) := by
  exact ⟨valid, periodicStrip.motif, [], rfl,
    Nat.le_refl _, by simp⟩

theorem packedOverlapReachable_step
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (countdown : Nat) (values : List Nat)
    (reachable :
      PackedOverlapReachable periodicStrip current next column
        (countdown + 1) values) :
    PackedOverlapReachable periodicStrip current next column
      countdown
      (Code.packedOverlapNativeStep
        periodicStrip current next column values) := by
  obtain ⟨valid, remaining, leading, rfl,
    countdownBound, suffix⟩ := reachable
  cases remaining with
  | nil =>
      exact ⟨valid, [], leading,
        Code.packedOverlapNativeStep_state_nil
          periodicStrip current next column valid,
        by omega, suffix⟩
  | cons cell remaining =>
      refine
        ⟨valid &&
            current.overlapsAtBool periodicStrip next column cell,
          remaining, leading ++ [cell], ?_, by omega, ?_⟩
      · exact
          Code.packedOverlapNativeStep_state_cons
            periodicStrip current next column valid cell remaining
      · simpa [List.append_assoc] using suffix

/-- The complete motif countdown reuses the polynomial body envelope. -/
theorem packedOverlapFlatUniform
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    EvaluatorCodeFits
      (Code.flatIterate Code.packedOverlapStepCode)
      (Encodable.encode periodicStrip.motif ::
        Code.packedOverlapState periodicStrip current next
          column true periodicStrip.motif)
      (Code.packedOverlapState periodicStrip current next column
        (current.overlapsColumnBool periodicStrip next column) [])
      (packedOverlapPolynomialSpaceBound
        periodicStrip current next column) where
  input_space := by
    have body :=
      packedOverlapBody periodicStrip current next column
        (Encodable.encode periodicStrip.motif)
        true periodicStrip.motif
    exact body.input_space.trans
      (packedOverlapBodyCost_le_polynomialSpaceBound
        periodicStrip current next column
        (Encodable.encode periodicStrip.motif)
        true periodicStrip.motif []
        (Nat.le_refl _) (by simp))
  output_space := by
    let result :=
      current.overlapsColumnBool periodicStrip next column
    have body :=
      packedOverlapBody periodicStrip current next column
        0 result []
    have input := body.input_space
    have cost :=
      packedOverlapBodyCost_le_polynomialSpaceBound
        periodicStrip current next column 0 result []
        periodicStrip.motif (Nat.zero_le _) (by simp)
    simp only [result] at input cost
    simp only [Code.packedOverlapState,
      encodedListSpace_cons] at input ⊢
    omega
  call continuation bound budget after := by
    apply
      EvaluatorCallFits.flatIterate_of_reachable_code_fits
        (step :=
          Code.packedOverlapNativeStep
            periodicStrip current next column)
        (bodyCost := fun _ _ =>
          packedOverlapPolynomialSpaceBound
            periodicStrip current next column)
        (invariant :=
          PackedOverlapReachable
            periodicStrip current next column)
    · intro countdown values reachable
      obtain ⟨valid, remaining, leading, rfl,
        countdownBound, suffix⟩ := reachable
      exact
        (packedOverlapBody periodicStrip current next column
          countdown valid remaining).mono
          (packedOverlapBodyCost_le_polynomialSpaceBound
            periodicStrip current next column countdown valid
            remaining leading countdownBound suffix)
    · exact packedOverlapReachable_initial
        periodicStrip current next column true
    · exact packedOverlapReachable_step
        periodicStrip current next column
    · intro countdown values reachable
      exact budget
    · rw [Code.packedOverlapNativeStep_iterate,
        Code.packedOverlapProcess_encode]
      simpa using after

def packedOverlapColumnCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) : Nat :=
  let result :=
    Code.packedOverlapState periodicStrip current next column
      (current.overlapsColumnBool periodicStrip next column) []
  getCost 6 result +
    (packedOverlapPolynomialSpaceBound
        periodicStrip current next column +
      packedOverlapLoopInputCost
        periodicStrip current next column)

/-- Fitted closed program for one packed shared column. -/
theorem packedOverlapColumn
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    EvaluatorCodeFits Code.packedOverlapColumnCode
      [Encodable.encode periodicStrip.motif,
        column.val + 1, column.val,
        current.assignmentWord, next.assignmentWord]
      [(current.overlapsColumnBool periodicStrip
        next column).toNat]
      (packedOverlapColumnCost
        periodicStrip current next column) := by
  let result :=
    Code.packedOverlapState periodicStrip current next column
      (current.overlapsColumnBool periodicStrip next column) []
  have loop :=
    comp
      (packedOverlapFlatUniform
        periodicStrip current next column)
      (packedOverlapLoopInput
        periodicStrip current next column)
  have projected := comp (get 6 result) loop
  simpa [Code.packedOverlapColumnCode,
    packedOverlapColumnCost, result,
    Code.packedOverlapState] using projected

theorem packedOverlapLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapLoopInputCost periodicStrip current next column ≤
      10000 *
        (encodedListSpace
          [4096 * (
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + current.assignmentWord +
            next.assignmentWord + 100) + 2000] + 1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let limit :=
    4096 * (motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode + motifCode +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  let unit := encodedListSpace [limit] + 1
  change
    packedOverlapLoopInputCost periodicStrip current next column ≤
      10000 * unit
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, encodedListSpace_cons, encodedListSpace_nil]
  have motifBits :=
    encodeNat_length_mono
      (show motifCode ≤ limit by simp only [limit]; omega)
  have columnBits :=
    encodeNat_length_mono
      (show column.val ≤ limit by simp only [limit]; omega)
  have columnSuccBits :=
    encodeNat_length_mono
      (show column.val + 1 ≤ limit by simp only [limit]; omega)
  have currentWordBits :=
    encodeNat_length_mono
      (show current.assignmentWord ≤ limit by
        simp only [limit]; omega)
  have nextWordBits :=
    encodeNat_length_mono
      (show next.assignmentWord ≤ limit by
        simp only [limit]; omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by simp only [limit]; omega)
  have columnTwoSuccBits :=
    encodeNat_length_mono
      (show column.val + 1 + 1 ≤ limit by
        simp only [limit]; omega)
  have currentWordSuccBits :=
    encodeNat_length_mono
      (show current.assignmentWord + 1 ≤ limit by
        simp only [limit]; omega)
  have nextWordSuccBits :=
    encodeNat_length_mono
      (show next.assignmentWord + 1 ≤ limit by
        simp only [limit]; omega)
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif)).length ≤
          (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifBits
  have motifSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif + 1)).length ≤
          (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifSuccBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  simp [packedOverlapLoopInputCost,
    prependCost, getCost, dropCost, headCost,
    idCost, nilCost, oneCost, zeroCost,
    tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    unitEq, zeroBits, oneBits]
  clear * - motifBitsRaw columnBits columnSuccBits
    currentWordBits nextWordBits motifSuccBitsRaw
    columnTwoSuccBits currentWordSuccBits nextWordSuccBits unitEq
  omega

theorem packedOverlapResultProjectionCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    getCost 6
        (Code.packedOverlapState periodicStrip current next column
          (current.overlapsColumnBool periodicStrip next column) []) ≤
      100 *
        (encodedListSpace
          [4096 * (
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + current.assignmentWord +
            next.assignmentWord + 100) + 2000] + 1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let limit :=
    4096 * (motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode + motifCode +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  let unit := encodedListSpace [limit] + 1
  change
    getCost 6
        (Code.packedOverlapState periodicStrip current next column
          (current.overlapsColumnBool periodicStrip next column) []) ≤
      100 * unit
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, encodedListSpace_cons, encodedListSpace_nil]
  have motifBits :=
    encodeNat_length_mono
      (show motifCode ≤ limit by simp only [limit]; omega)
  have columnBits :=
    encodeNat_length_mono
      (show column.val ≤ limit by simp only [limit]; omega)
  have columnSuccBits :=
    encodeNat_length_mono
      (show column.val + 1 ≤ limit by simp only [limit]; omega)
  have currentWordBits :=
    encodeNat_length_mono
      (show current.assignmentWord ≤ limit by
        simp only [limit]; omega)
  have nextWordBits :=
    encodeNat_length_mono
      (show next.assignmentWord ≤ limit by
        simp only [limit]; omega)
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif)).length ≤
          (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  cases overlap :
      current.overlapsColumnBool periodicStrip next column <;>
    simp [Code.packedOverlapState,
      getCost, dropCost, headCost, idCost,
      nilCost, tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq, zeroBits, oneBits, twoBits] <;>
    clear * - motifBitsRaw columnBits columnSuccBits
      currentWordBits nextWordBits unitEq <;>
    omega

private theorem packedOverlapColumnBudget
    (unit projection space input : Nat)
    (projectionBound : projection ≤ 100 * unit)
    (spaceBound :
      space ≤ 1000000000000000000000000000000000 * unit)
    (inputBound : input ≤ 10000 * unit) :
    projection + (space + input) ≤
      2000000000000000000000000000000000 * unit := by
  omega

theorem packedOverlapColumnCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapColumnCost periodicStrip current next column ≤
      2000000000000000000000000000000000 *
        (encodedListSpace
          [4096 * (
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + current.assignmentWord +
            next.assignmentWord + 100) + 2000] + 1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let limit :=
    4096 * (motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode + motifCode +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  let unit := encodedListSpace [limit] + 1
  change
    packedOverlapColumnCost periodicStrip current next column ≤
      2000000000000000000000000000000000 * unit
  have inputGlobal :
      packedOverlapLoopInputCost periodicStrip current next column ≤
        10000 * unit := by
    simpa [motifCode, limit, unit] using
      packedOverlapLoopInputCost_le_linear
        periodicStrip current next column
  have projectionGlobal :
      getCost 6
          (Code.packedOverlapState periodicStrip current next column
            (current.overlapsColumnBool periodicStrip next column) []) ≤
        100 * unit := by
    simpa [motifCode, limit, unit] using
      packedOverlapResultProjectionCost_le_linear
        periodicStrip current next column
  simp only [packedOverlapColumnCost,
    packedOverlapPolynomialSpaceBound]
  exact
    packedOverlapColumnBudget unit _ _ _
      projectionGlobal (Nat.le_refl _) inputGlobal

def packedOverlapColumnArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) : Nat :=
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  let rest1 :=
    prependCost values [current.assignmentWord]
      [next.assignmentWord]
      (getCost 1 values) (getCost 2 values)
  let restColumn :=
    prependCost values [column.val]
      [current.assignmentWord, next.assignmentWord]
      (numeralCost column.val values) rest1
  let restSuccessor :=
    prependCost values [column.val + 1]
      [column.val, current.assignmentWord, next.assignmentWord]
      (numeralCost (column.val + 1) values) restColumn
  prependCost values [Encodable.encode periodicStrip.motif]
    [column.val + 1, column.val,
      current.assignmentWord, next.assignmentWord]
    (getCost 0 values) restSuccessor

theorem packedOverlapColumnArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    EvaluatorCodeFits
      (Code.packedOverlapColumnArgumentsCode column)
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      [Encodable.encode periodicStrip.motif,
        column.val + 1, column.val,
        current.assignmentWord, next.assignmentWord]
      (packedOverlapColumnArgumentsCost
        periodicStrip current next column) := by
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  have rest1 := prepend (get 1 values) (get 2 values)
  have restColumn := prepend (numeral column.val values) rest1
  have restSuccessor :=
    prepend (numeral (column.val + 1) values) restColumn
  have result := prepend (get 0 values) restSuccessor
  simpa [Code.packedOverlapColumnArgumentsCode,
    packedOverlapColumnArgumentsCost, Code.numeral,
    numeralCost, prependCost, values] using result

def packedOverlapColumnAtCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) : Nat :=
  packedOverlapColumnCost periodicStrip current next column +
    packedOverlapColumnArgumentsCost
      periodicStrip current next column

theorem packedOverlapColumnAt
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    EvaluatorCodeFits (Code.packedOverlapColumnAtCode column)
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      [(current.overlapsColumnBool periodicStrip
        next column).toNat]
      (packedOverlapColumnAtCost
        periodicStrip current next column) := by
  simpa [Code.packedOverlapColumnAtCode,
    packedOverlapColumnAtCost] using
    comp
      (packedOverlapColumn periodicStrip current next column)
      (packedOverlapColumnArguments
        periodicStrip current next column)

def packedOverlapLastTwoCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  boolAndCost values
    (current.overlapsColumnBool
      periodicStrip next (2 : Fin 4)).toNat
    (current.overlapsColumnBool
      periodicStrip next (3 : Fin 4)).toNat
    (packedOverlapColumnAtCost
      periodicStrip current next (2 : Fin 4))
    (packedOverlapColumnAtCost
      periodicStrip current next (3 : Fin 4))

theorem packedOverlapLastTwo
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.packedOverlapColumnAtCode (2 : Fin 4))
        (Code.packedOverlapColumnAtCode (3 : Fin 4)))
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      [(current.overlapsColumnBool
          periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool
          periodicStrip next (3 : Fin 4)).toNat]
      (packedOverlapLastTwoCost
        periodicStrip current next) := by
  have combined :=
    boolAnd
      (packedOverlapColumnAt
        periodicStrip current next (2 : Fin 4))
      (packedOverlapColumnAt
        periodicStrip current next (3 : Fin 4))
  cases second :
      current.overlapsColumnBool
        periodicStrip next (2 : Fin 4) <;>
    cases third :
      current.overlapsColumnBool
        periodicStrip next (3 : Fin 4) <;>
    simpa [packedOverlapLastTwoCost, second, third] using combined

def packedOverlapLastThreeCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  let tailTag :=
    (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
      current.overlapsColumnBool periodicStrip next (3 : Fin 4)).toNat
  boolAndCost values
    (current.overlapsColumnBool
      periodicStrip next (1 : Fin 4)).toNat
    tailTag
    (packedOverlapColumnAtCost
      periodicStrip current next (1 : Fin 4))
    (packedOverlapLastTwoCost periodicStrip current next)

theorem packedOverlapLastThree
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.packedOverlapColumnAtCode (1 : Fin 4))
        (Code.boolAnd
          (Code.packedOverlapColumnAtCode (2 : Fin 4))
          (Code.packedOverlapColumnAtCode (3 : Fin 4))))
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      [(current.overlapsColumnBool
          periodicStrip next (1 : Fin 4) &&
        (current.overlapsColumnBool
            periodicStrip next (2 : Fin 4) &&
          current.overlapsColumnBool
            periodicStrip next (3 : Fin 4))).toNat]
      (packedOverlapLastThreeCost
        periodicStrip current next) := by
  have combined :=
    boolAnd
      (packedOverlapColumnAt
        periodicStrip current next (1 : Fin 4))
      (packedOverlapLastTwo periodicStrip current next)
  cases first :
      current.overlapsColumnBool
        periodicStrip next (1 : Fin 4) <;>
    cases second :
      current.overlapsColumnBool
        periodicStrip next (2 : Fin 4) <;>
    cases third :
      current.overlapsColumnBool
        periodicStrip next (3 : Fin 4) <;>
    simpa [packedOverlapLastThreeCost,
      first, second, third] using combined

def packedOverlapColumnsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  let tailTag :=
    (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool
          periodicStrip next (3 : Fin 4))).toNat
  boolAndCost values
    (current.overlapsColumnBool
      periodicStrip next (0 : Fin 4)).toNat
    tailTag
    (packedOverlapColumnAtCost
      periodicStrip current next (0 : Fin 4))
    (packedOverlapLastThreeCost periodicStrip current next)

theorem packedOverlapColumns
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedOverlapColumnsCode
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      [((List.finRange 4).all fun column =>
        current.overlapsColumnBool periodicStrip next column).toNat]
      (packedOverlapColumnsCost
        periodicStrip current next) := by
  have combined :=
    boolAnd
      (packedOverlapColumnAt
        periodicStrip current next (0 : Fin 4))
      (packedOverlapLastThree periodicStrip current next)
  cases zero :
      current.overlapsColumnBool
        periodicStrip next (0 : Fin 4) <;>
    cases one :
      current.overlapsColumnBool
        periodicStrip next (1 : Fin 4) <;>
    cases two :
      current.overlapsColumnBool
        periodicStrip next (2 : Fin 4) <;>
    cases three :
      current.overlapsColumnBool
        periodicStrip next (3 : Fin 4) <;>
    simpa [Code.packedOverlapColumnsCode,
      packedOverlapColumnsCost, List.finRange_succ,
      zero, one, two, three] using combined

/-- One arithmetic envelope shared by all four fixed overlap-column calls.
The deliberately repeated motif term absorbs every encoded suffix retained by
the streaming implementation; the fixed column indices are absorbed by the
constant slack. -/
def packedOverlapColumnsLimit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  4096 * (
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    current.assignmentWord + next.assignmentWord + 200) + 3000

/-- Uniform workspace unit for the complete four-column overlap predicate. -/
def packedOverlapColumnsUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  encodedListSpace
    [packedOverlapColumnsLimit periodicStrip current next] + 1

private theorem packedOverlapColumnUnit_le_columnsUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    encodedListSpace
          [4096 * (
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + current.assignmentWord +
            next.assignmentWord + 100) + 2000] + 1 ≤
      packedOverlapColumnsUnit periodicStrip current next := by
  let small :=
    4096 * (
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      column.val + current.assignmentWord +
      next.assignmentWord + 100) + 2000
  let large := packedOverlapColumnsLimit periodicStrip current next
  have valueBound : small ≤ large := by
    simp only [small, large, packedOverlapColumnsLimit]
    have columnLt : column.val < 4 := column.isLt
    omega
  have bitsBound := encodeNat_length_mono valueBound
  simpa [small, large, packedOverlapColumnsUnit,
    encodedListSpace_cons, encodedListSpace_nil] using bitsBound

private theorem packedOverlapColumnCost_le_columnsUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapColumnCost periodicStrip current next column ≤
      2000000000000000000000000000000000 *
        packedOverlapColumnsUnit periodicStrip current next := by
  exact (packedOverlapColumnCost_le_linear
    periodicStrip current next column).trans
      (Nat.mul_le_mul_left _
        (packedOverlapColumnUnit_le_columnsUnit
          periodicStrip current next column))

set_option maxHeartbeats 800000 in
private theorem packedOverlapColumnArgumentsCost_le_columnsUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapColumnArgumentsCost periodicStrip current next column ≤
      1000000000 * packedOverlapColumnsUnit periodicStrip current next := by
  let limit := packedOverlapColumnsLimit periodicStrip current next
  let unit := packedOverlapColumnsUnit periodicStrip current next
  have motifBound : Encodable.encode periodicStrip.motif ≤ limit := by
    simp only [limit, packedOverlapColumnsLimit]
    omega
  have columnBound : column.val ≤ limit := by
    simp only [limit, packedOverlapColumnsLimit]
    omega
  have columnSuccBound : column.val + 1 ≤ limit := by
    simp only [limit, packedOverlapColumnsLimit]
    omega
  have currentWordBound : current.assignmentWord ≤ limit := by
    simp only [limit, packedOverlapColumnsLimit]
    omega
  have nextWordBound : next.assignmentWord ≤ limit := by
    simp only [limit, packedOverlapColumnsLimit]
    omega
  have motifBits := encodeNat_length_mono motifBound
  have columnBits := encodeNat_length_mono columnBound
  have columnSuccBits := encodeNat_length_mono columnSuccBound
  have currentWordBits := encodeNat_length_mono currentWordBound
  have nextWordBits := encodeNat_length_mono nextWordBound
  have motifSuccBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip.motif + 1 ≤ limit by
      simp only [limit, packedOverlapColumnsLimit]
      omega)
  have currentWordSuccBits := encodeNat_length_mono
    (show current.assignmentWord + 1 ≤ limit by
      simp only [limit, packedOverlapColumnsLimit]
      omega)
  have nextWordSuccBits := encodeNat_length_mono
    (show next.assignmentWord + 1 ≤ limit by
      simp only [limit, packedOverlapColumnsLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    dsimp only [unit, limit]
    simp [packedOverlapColumnsUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have numeralColumnCost :
      addConstCost column.val [0] ≤ 1000000 * unit := by
    have raw := addConstCost_le column.val [0]
    have columnLt : column.val < 4 := column.isLt
    have unitPositive : 1 ≤ unit := by
      simp [unit, packedOverlapColumnsUnit]
    have zeroBits :
        (Computability.encodeNat 0).length = 0 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil,
      zeroBits] at raw
    nlinarith
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedOverlapColumnArgumentsCost,
    prependCost, numeralCost, addConstCost,
    getCost, dropCost, headCost, idCost,
    nilCost, zeroCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits]
  clear * - motifBits columnBits columnSuccBits
    currentWordBits nextWordBits motifSuccBits
    currentWordSuccBits nextWordSuccBits numeralColumnCost unitEq
  omega

private theorem packedOverlapColumnAtCost_le_columnsUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapColumnAtCost periodicStrip current next column ≤
      3000000000000000000000000000000000 *
        packedOverlapColumnsUnit periodicStrip current next := by
  have columnCost := packedOverlapColumnCost_le_columnsUnit
    periodicStrip current next column
  have argumentsCost := packedOverlapColumnArgumentsCost_le_columnsUnit
    periodicStrip current next column
  simp only [packedOverlapColumnAtCost]
  omega

set_option maxHeartbeats 2000000 in
/-- The complete fixed four-column conjunction has one input-linear
evaluator-space majorant. -/
theorem packedOverlapColumnsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedOverlapColumnsCost periodicStrip current next ≤
      10000000000000000000000000000000000000000000000 *
        packedOverlapColumnsUnit periodicStrip current next := by
  let unit := packedOverlapColumnsUnit periodicStrip current next
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  let baseBudget :=
    3000000000000000000000000000000000 * unit
  let secondBudget := 1000 * (baseBudget + 1)
  let thirdBudget := 1000 * (secondBudget + 1)
  let finalBudget := 1000 * (thirdBudget + 1)
  have unitPositive : 1 ≤ unit := by
    simp [unit, packedOverlapColumnsUnit]
  have unitEq :
      unit =
        (Computability.encodeNat
          (packedOverlapColumnsLimit periodicStrip current next)).length +
            2 := by
    simp [unit, packedOverlapColumnsUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have valuesSpace : encodedListSpace values ≤ 10 * unit := by
    have motifBound :
        Encodable.encode periodicStrip.motif ≤
          packedOverlapColumnsLimit periodicStrip current next := by
      simp only [packedOverlapColumnsLimit]
      omega
    have currentBound :
        current.assignmentWord ≤
          packedOverlapColumnsLimit periodicStrip current next := by
      simp only [packedOverlapColumnsLimit]
      omega
    have nextBound :
        next.assignmentWord ≤
          packedOverlapColumnsLimit periodicStrip current next := by
      simp only [packedOverlapColumnsLimit]
      omega
    have motifBits := encodeNat_length_mono motifBound
    have currentBits := encodeNat_length_mono currentBound
    have nextBits := encodeNat_length_mono nextBound
    simp only [values, encodedListSpace_cons, encodedListSpace_nil]
    rw [unitEq]
    omega
  have headBits :
      (Computability.encodeNat values.headI).length ≤ 10 * unit := by
    simp [values] at valuesSpace ⊢
    omega
  have headSuccBits :
      (Computability.encodeNat (values.headI + 1)).length ≤
        20 * unit := by
    have successor := encodeNat_succ_length_le values.headI
    have successor' :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using successor
    omega
  have cost0 := packedOverlapColumnAtCost_le_columnsUnit
    periodicStrip current next (0 : Fin 4)
  have cost1 := packedOverlapColumnAtCost_le_columnsUnit
    periodicStrip current next (1 : Fin 4)
  have cost2 := packedOverlapColumnAtCost_le_columnsUnit
    periodicStrip current next (2 : Fin 4)
  have cost3 := packedOverlapColumnAtCost_le_columnsUnit
    periodicStrip current next (3 : Fin 4)
  have valuesBase : encodedListSpace values ≤ baseBudget := by
    simp only [baseBudget]
    omega
  have headBase :
      (Computability.encodeNat values.headI).length ≤ baseBudget := by
    simp only [baseBudget]
    omega
  have headSuccBase :
      (Computability.encodeNat (values.headI + 1)).length ≤
        baseBudget := by
    simp only [baseBudget]
    omega
  have cost0Base :
      packedOverlapColumnAtCost periodicStrip current next (0 : Fin 4) ≤
        baseBudget := by simpa [baseBudget, unit] using cost0
  have cost1Base :
      packedOverlapColumnAtCost periodicStrip current next (1 : Fin 4) ≤
        baseBudget := by simpa [baseBudget, unit] using cost1
  have cost2Base :
      packedOverlapColumnAtCost periodicStrip current next (2 : Fin 4) ≤
        baseBudget := by simpa [baseBudget, unit] using cost2
  have cost3Base :
      packedOverlapColumnAtCost periodicStrip current next (3 : Fin 4) ≤
        baseBudget := by simpa [baseBudget, unit] using cost3
  have tag0 :
      (current.overlapsColumnBool
        periodicStrip next (0 : Fin 4)).toNat ≤ 1 := by
    cases current.overlapsColumnBool periodicStrip next (0 : Fin 4) <;>
      simp
  have tag1 :
      (current.overlapsColumnBool
        periodicStrip next (1 : Fin 4)).toNat ≤ 1 := by
    cases current.overlapsColumnBool periodicStrip next (1 : Fin 4) <;>
      simp
  have tag2 :
      (current.overlapsColumnBool
        periodicStrip next (2 : Fin 4)).toNat ≤ 1 := by
    cases current.overlapsColumnBool periodicStrip next (2 : Fin 4) <;>
      simp
  have tag3 :
      (current.overlapsColumnBool
        periodicStrip next (3 : Fin 4)).toNat ≤ 1 := by
    cases current.overlapsColumnBool periodicStrip next (3 : Fin 4) <;>
      simp
  have lastTwoBound :
      packedOverlapLastTwoCost periodicStrip current next ≤
        secondBudget := by
    have bound := boolAndCost_le_budget values
      (current.overlapsColumnBool
        periodicStrip next (2 : Fin 4)).toNat
      (current.overlapsColumnBool
        periodicStrip next (3 : Fin 4)).toNat
      (packedOverlapColumnAtCost
        periodicStrip current next (2 : Fin 4))
      (packedOverlapColumnAtCost
        periodicStrip current next (3 : Fin 4))
      baseBudget tag2 tag3 valuesBase headBase headSuccBase
      cost2Base cost3Base (by
        simp only [baseBudget]
        exact Nat.mul_pos (by norm_num) (by omega))
    simpa [packedOverlapLastTwoCost, values,
      secondBudget] using bound
  have valuesSecond : encodedListSpace values ≤ secondBudget := by
    simp only [secondBudget]
    exact valuesBase.trans (by omega)
  have headSecond :
      (Computability.encodeNat values.headI).length ≤ secondBudget := by
    exact headBase.trans (by simp only [secondBudget]; omega)
  have headSuccSecond :
      (Computability.encodeNat (values.headI + 1)).length ≤
        secondBudget := by
    exact headSuccBase.trans (by simp only [secondBudget]; omega)
  have cost1Second :
      packedOverlapColumnAtCost periodicStrip current next (1 : Fin 4) ≤
        secondBudget :=
    cost1Base.trans (by simp only [secondBudget]; omega)
  have tagLastTwo :
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool
          periodicStrip next (3 : Fin 4)).toNat ≤ 1 := by
    cases current.overlapsColumnBool periodicStrip next (2 : Fin 4) <;>
      cases current.overlapsColumnBool
        periodicStrip next (3 : Fin 4) <;> simp
  have lastThreeBound :
      packedOverlapLastThreeCost periodicStrip current next ≤
        thirdBudget := by
    have bound := boolAndCost_le_budget values
      (current.overlapsColumnBool
        periodicStrip next (1 : Fin 4)).toNat
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool
          periodicStrip next (3 : Fin 4)).toNat
      (packedOverlapColumnAtCost
        periodicStrip current next (1 : Fin 4))
      (packedOverlapLastTwoCost periodicStrip current next)
      secondBudget tag1 tagLastTwo valuesSecond headSecond
      headSuccSecond cost1Second lastTwoBound
      (by
        simp only [secondBudget]
        exact Nat.mul_pos (by norm_num) (Nat.succ_pos _))
    simpa [packedOverlapLastThreeCost, values,
      thirdBudget] using bound
  have valuesThird : encodedListSpace values ≤ thirdBudget :=
    valuesSecond.trans (by simp only [thirdBudget]; omega)
  have headThird :
      (Computability.encodeNat values.headI).length ≤ thirdBudget :=
    headSecond.trans (by simp only [thirdBudget]; omega)
  have headSuccThird :
      (Computability.encodeNat (values.headI + 1)).length ≤
        thirdBudget :=
    headSuccSecond.trans (by simp only [thirdBudget]; omega)
  have cost0Third :
      packedOverlapColumnAtCost periodicStrip current next (0 : Fin 4) ≤
        thirdBudget :=
    cost0Base.trans (by
      simp only [thirdBudget, secondBudget]
      omega)
  have tagLastThree :
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
        (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
          current.overlapsColumnBool
            periodicStrip next (3 : Fin 4))).toNat ≤ 1 := by
    cases current.overlapsColumnBool periodicStrip next (1 : Fin 4) <;>
      cases current.overlapsColumnBool
        periodicStrip next (2 : Fin 4) <;>
      cases current.overlapsColumnBool
        periodicStrip next (3 : Fin 4) <;> simp
  have wholeBound :
      packedOverlapColumnsCost periodicStrip current next ≤
        finalBudget := by
    have bound := boolAndCost_le_budget values
      (current.overlapsColumnBool
        periodicStrip next (0 : Fin 4)).toNat
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
        (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
          current.overlapsColumnBool
            periodicStrip next (3 : Fin 4))).toNat
      (packedOverlapColumnAtCost
        periodicStrip current next (0 : Fin 4))
      (packedOverlapLastThreeCost periodicStrip current next)
      thirdBudget tag0 tagLastThree valuesThird headThird
      headSuccThird cost0Third lastThreeBound
      (by
        simp only [thirdBudget]
        exact Nat.mul_pos (by norm_num) (Nat.succ_pos _))
    simpa [packedOverlapColumnsCost, values,
      finalBudget] using bound
  exact wholeBound.trans (by
    simp only [finalBudget, thirdBudget, secondBudget, baseBudget]
    omega)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
