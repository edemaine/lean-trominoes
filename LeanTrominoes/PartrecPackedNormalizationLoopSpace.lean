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

set_option maxHeartbeats 800000 in
theorem packedNormalizationBodyCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) :
    packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining ≤
      1000000000000000000000000000000000 *
        (encodedListSpace
          [4096 * (countdown +
            periodicStrip.period + packed.phase +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode remaining +
            Encodable.encode remaining +
            Encodable.encode remaining +
            column.val + packed.assignmentWord + 100) + 2000] +
          1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let remainingCode := Encodable.encode remaining
  let limit :=
    4096 * (countdown +
      periodicStrip.period + packed.phase +
      motifCode + motifCode + motifCode +
      remainingCode + remainingCode + remainingCode +
      column.val + packed.assignmentWord + 100) + 2000
  change
    packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining ≤
      1000000000000000000000000000000000 *
        (encodedListSpace [limit] + 1)
  have countdownBound : countdown ≤ limit := by
    simp only [limit]
    omega
  have periodBound : periodicStrip.period ≤ limit := by
    simp only [limit]
    omega
  have phaseBound : packed.phase ≤ limit := by
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
  have wordBound : packed.assignmentWord ≤ limit := by
    simp only [limit]
    omega
  have countdownBits := encodeNat_length_mono countdownBound
  have countdownPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le countdown).trans countdownBound)
  have periodBits := encodeNat_length_mono periodBound
  have phaseBits := encodeNat_length_mono phaseBound
  have motifBits := encodeNat_length_mono motifBound
  have remainingBits := encodeNat_length_mono remainingBound
  have columnBits := encodeNat_length_mono columnBound
  have wordBits := encodeNat_length_mono wordBound
  have countdownSuccBits :=
    encodeNat_length_mono
      (show countdown + 1 ≤ limit by
        simp only [limit]
        omega)
  have periodSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.period + 1 ≤ limit by
        simp only [limit]
        omega)
  have phaseSuccBits :=
    encodeNat_length_mono
      (show packed.phase + 1 ≤ limit by
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
  have wordSuccBits :=
    encodeNat_length_mono
      (show packed.assignmentWord + 1 ≤ limit by
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
              (Code.packedNormalizationNativeStep periodicStrip packed
                column
                (Code.packedNormalizationState periodicStrip packed
                  column valid [])) ≤
            10 * ((Computability.encodeNat limit).length + 2) := by
        rw [Code.packedNormalizationNativeStep_state_nil]
        cases valid <;>
          simp [Code.packedNormalizationState,
            encodedListSpace_cons, encodedListSpace_nil,
            motifCode, zeroBits, oneBits] at * <;>
          omega
      cases countdown <;>
        cases valid <;>
        simp [packedNormalizationBodyCost,
          packedNormalizationStepCost,
          flatCountdownBodyCost,
          flatCountdownSuccBranchCost,
          branchZeroZeroCost, branchZeroTestCost,
          prependCost, getCost, dropCost, idCost,
          headCost, nilCost, oneCost, zeroCost,
          zeroPrimeCost, tailCost, succCost,
          Code.packedNormalizationState,
          encodedListSpace_cons, encodedListSpace_nil,
          motifCode, remainingCode, limit,
          zeroBits, oneBits, twoBits] at * <;>
        clear * - countdownBits countdownPredBits
          periodBits phaseBits motifBits remainingBits
          columnBits wordBits countdownSuccBits
          periodSuccBits phaseSuccBits motifSuccBits
          remainingSuccBits columnSuccBits wordSuccBits
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
      let normalizedLimit :=
        1024 * (periodicStrip.period + packed.phase +
          motifCode + motifCode + motifCode +
          cellCode + column.val + packed.assignmentWord + 100) +
          1000
      have normalizedNumeric : normalizedLimit ≤ limit := by
        simp only [normalizedLimit, limit]
        omega
      have normalizedBits :=
        encodeNat_length_mono normalizedNumeric
      have normalizedLocal :=
        packedNormalizedAtCost_le_linear
          periodicStrip.period packed.phase periodicStrip.motif
          column.val cell packed.assignmentWord
      have normalizedGlobal :
          packedNormalizedAtCost periodicStrip.period packed.phase
              periodicStrip.motif column.val cell
              packed.assignmentWord ≤
            1000000000000000000000000000000 *
              (encodedListSpace [limit] + 1) := by
        have aligned :
            packedNormalizedAtCost periodicStrip.period packed.phase
                periodicStrip.motif column.val cell
                packed.assignmentWord ≤
              1000000000000000000000000000000 *
                (encodedListSpace [normalizedLimit] + 1) := by
          simpa [packedNormalizedAtSpaceBound,
            normalizedLimit, motifCode, cellCode] using
            normalizedLocal
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
              (Computability.encodeNat periodicStrip.period).length +
              (Computability.encodeNat packed.phase).length +
              (Computability.encodeNat column.val).length +
              (Computability.encodeNat
                packed.assignmentWord).length ≤
            6 * (Computability.encodeNat limit).length := by
        clear * - motifBitsRaw tailBitsRaw periodBits phaseBits
          columnBits wordBits
        omega
      have nextStateSpace :
          encodedListSpace
              (Code.packedNormalizationNativeStep periodicStrip packed
                column
                (Code.packedNormalizationState periodicStrip packed
                  column valid (cell :: remaining))) ≤
            10 * ((Computability.encodeNat limit).length + 2) := by
        rw [Code.packedNormalizationNativeStep_state_cons]
        cases valid <;>
          cases normalized :
            packed.normalizedAtBool periodicStrip column cell <;>
          simp [Code.packedNormalizationState,
            encodedListSpace_cons, encodedListSpace_nil,
            zeroBits, oneBits] <;>
          clear * - nextStateFieldBits <;>
          omega
      cases countdown with
      | zero =>
          cases valid <;>
            simp [packedNormalizationBodyCost,
              flatCountdownBodyCost, zeroPrimeCost,
              Code.packedNormalizationState,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, remainingCode, cellCode, tailCode,
              limit, zeroBits, oneBits, twoBits] at * <;>
            clear * - countdownBits countdownPredBits
              periodBits phaseBits motifBits remainingBits
              columnBits wordBits countdownSuccBits
              periodSuccBits phaseSuccBits motifSuccBits
              remainingSuccBits columnSuccBits wordSuccBits
              cellBits tailBits constructorBits cellSuccBits
              tailSuccBits nextStateSpace <;>
            omega
      | succ countdown =>
          cases valid <;>
            cases normalized :
              packed.normalizedAtBool periodicStrip column cell <;>
            simp [packedNormalizationBodyCost,
              packedNormalizationStepCost,
              packedNormalizationConsStepCost,
              packedNormalizationUpdatedValidCost,
              packedNormalizationHeadValidCost,
              packedNormalizationAtArgumentsCost,
              packedNormalizationHeadCost,
              packedNormalizationTailCost,
              packedNormalizationViewCost,
              flatCountdownBodyCost,
              flatCountdownSuccBranchCost,
              branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, boolAndCost,
              normalizeBoolCost, prependCost,
              getCost, dropCost, idCost, headCost,
              nilCost, oneCost, zeroCost, zeroPrimeCost,
              tailCost, succCost,
              Code.packedNormalizationState,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, remainingCode, cellCode, tailCode,
              limit, normalized,
              zeroBits, oneBits, twoBits] at * <;>
            clear * - countdownBits countdownPredBits
              periodBits phaseBits motifBits remainingBits
              columnBits wordBits countdownSuccBits
              periodSuccBits phaseSuccBits motifSuccBits
              remainingSuccBits columnSuccBits wordSuccBits
              cellBits tailBits constructorBits cellSuccBits
              tailSuccBits viewGlobal normalizedGlobal
              nextStateSpace <;>
            omega

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

/-- Maximum of the exact body costs over every suffix of one motif, for a
fixed countdown. -/
def packedNormalizationSuffixSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) : List Cell → Nat
  | [] =>
      max
        (packedNormalizationBodyCost periodicStrip packed column
          countdown false [])
        (packedNormalizationBodyCost periodicStrip packed column
          countdown true [])
  | cell :: remaining =>
      max
        (packedNormalizationBodyCost periodicStrip packed column
          countdown false (cell :: remaining))
        (max
          (packedNormalizationBodyCost periodicStrip packed column
            countdown true (cell :: remaining))
          (packedNormalizationSuffixSpaceBound periodicStrip packed
            column countdown remaining))

theorem packedNormalizationBodyCost_le_suffixSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (valid : Bool)
    (leading remaining : List Cell) :
    packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining ≤
      packedNormalizationSuffixSpaceBound periodicStrip packed
        column countdown (leading ++ remaining) := by
  induction leading with
  | nil =>
      cases remaining with
      | nil =>
          cases valid
          · simp [packedNormalizationSuffixSpaceBound]
          · simp [packedNormalizationSuffixSpaceBound]
      | cons cell remaining =>
          cases valid
          · exact Nat.le_max_left _ _
          · exact
              (Nat.le_max_left _ _).trans
                (Nat.le_max_right _ _)
  | cons cell leading induction =>
      have bounded := induction
      simp only [List.cons_append,
        packedNormalizationSuffixSpaceBound]
      exact bounded.trans
        ((Nat.le_max_right _ _).trans
          (Nat.le_max_right _ _))

/-- Maximum of the suffix envelopes for every countdown up to the supplied
limit. -/
def packedNormalizationSpaceBoundUpTo
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    Nat → Nat
  | 0 =>
      packedNormalizationSuffixSpaceBound periodicStrip packed
        column 0 periodicStrip.motif
  | limit + 1 =>
      max
        (packedNormalizationSuffixSpaceBound periodicStrip packed
          column (limit + 1) periodicStrip.motif)
        (packedNormalizationSpaceBoundUpTo periodicStrip packed
          column limit)

theorem packedNormalizationSuffixSpaceBound_le_upTo
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown limit : Nat) (bounded : countdown ≤ limit) :
    packedNormalizationSuffixSpaceBound periodicStrip packed
        column countdown periodicStrip.motif ≤
      packedNormalizationSpaceBoundUpTo periodicStrip packed
        column limit := by
  induction limit with
  | zero =>
      have countdownZero : countdown = 0 := by omega
      subst countdown
      simp [packedNormalizationSpaceBoundUpTo]
  | succ limit induction =>
      by_cases top : countdown = limit + 1
      · subst countdown
        simp [packedNormalizationSpaceBoundUpTo]
      · have below : countdown ≤ limit := by omega
        have previous := induction below
        exact previous.trans (by
          simp [packedNormalizationSpaceBoundUpTo])

/-- One workspace envelope for every typed state reachable during the
complete normalization scan. -/
def packedNormalizationSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  packedNormalizationSpaceBoundUpTo periodicStrip packed column
    (Encodable.encode periodicStrip.motif)

theorem packedNormalizationBodyCost_le_spaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (valid : Bool)
    (remaining leading : List Cell)
    (countdownBound :
      countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining ≤
      packedNormalizationSpaceBound periodicStrip packed column := by
  have bodyToSuffix :=
    packedNormalizationBodyCost_le_suffixSpaceBound
      periodicStrip packed column countdown valid leading remaining
  rw [← suffix] at bodyToSuffix
  exact bodyToSuffix.trans
    (packedNormalizationSuffixSpaceBound_le_upTo
      periodicStrip packed column countdown
      (Encodable.encode periodicStrip.motif) countdownBound)

def packedNormalizationPolynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  1000000000000000000000000000000000 *
    (encodedListSpace
      [4096 * (periodicStrip.period + packed.phase +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        Encodable.encode periodicStrip.motif +
        column.val + packed.assignmentWord + 100) + 2000] +
      1)

theorem packedNormalizationBodyCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (valid : Bool)
    (remaining leading : List Cell)
    (countdownBound :
      countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining ≤
      packedNormalizationPolynomialSpaceBound
        periodicStrip packed column := by
  let motifCode := Encodable.encode periodicStrip.motif
  let remainingCode := Encodable.encode remaining
  let localLimit :=
    4096 * (countdown +
      periodicStrip.period + packed.phase +
      motifCode + motifCode + motifCode +
      remainingCode + remainingCode + remainingCode +
      column.val + packed.assignmentWord + 100) + 2000
  let globalLimit :=
    4096 * (periodicStrip.period + packed.phase +
      motifCode + motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode +
      column.val + packed.assignmentWord + 100) + 2000
  have remainingBound : remainingCode ≤ motifCode := by
    simp only [remainingCode, motifCode]
    rw [suffix]
    exact encode_list_suffix_le leading remaining
  have numeric : localLimit ≤ globalLimit := by
    simp only [localLimit, globalLimit]
    omega
  have bits := encodeNat_length_mono numeric
  have body :=
    packedNormalizationBodyCost_le_linear periodicStrip packed
      column countdown valid remaining
  have bodyLocal :
      packedNormalizationBodyCost periodicStrip packed column
          countdown valid remaining ≤
        1000000000000000000000000000000000 *
          (encodedListSpace [localLimit] + 1) := by
    simpa [localLimit, motifCode, remainingCode] using body
  simp only [packedNormalizationPolynomialSpaceBound,
    encodedListSpace_cons, encodedListSpace_nil]
  change
    packedNormalizationBodyCost periodicStrip packed column
        countdown valid remaining ≤
      1000000000000000000000000000000000 *
        ((Computability.encodeNat globalLimit).length + 1 + 1)
  simp only [encodedListSpace_cons,
    encodedListSpace_nil] at bodyLocal
  exact bodyLocal.trans
    (Nat.mul_le_mul_left
      1000000000000000000000000000000000
      (by omega))

theorem packedNormalizationSuffixSpaceBound_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (remaining leading : List Cell)
    (countdownBound :
      countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedNormalizationSuffixSpaceBound periodicStrip packed
        column countdown remaining ≤
      packedNormalizationPolynomialSpaceBound
        periodicStrip packed column := by
  induction remaining generalizing leading with
  | nil =>
      simp only [packedNormalizationSuffixSpaceBound]
      apply Nat.max_le.mpr
      constructor
      · exact
          packedNormalizationBodyCost_le_polynomialSpaceBound
            periodicStrip packed column countdown false []
            leading countdownBound suffix
      · exact
          packedNormalizationBodyCost_le_polynomialSpaceBound
            periodicStrip packed column countdown true []
            leading countdownBound suffix
  | cons cell remaining induction =>
      simp only [packedNormalizationSuffixSpaceBound]
      apply Nat.max_le.mpr
      constructor
      · exact
          packedNormalizationBodyCost_le_polynomialSpaceBound
            periodicStrip packed column countdown false
            (cell :: remaining) leading countdownBound suffix
      · apply Nat.max_le.mpr
        constructor
        · exact
            packedNormalizationBodyCost_le_polynomialSpaceBound
              periodicStrip packed column countdown true
              (cell :: remaining) leading countdownBound suffix
        · apply induction (leading := leading ++ [cell])
          simpa [List.append_assoc] using suffix

theorem packedNormalizationSpaceBoundUpTo_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (limit : Nat)
    (limitBound :
      limit ≤ Encodable.encode periodicStrip.motif) :
    packedNormalizationSpaceBoundUpTo periodicStrip packed
        column limit ≤
      packedNormalizationPolynomialSpaceBound
        periodicStrip packed column := by
  induction limit with
  | zero =>
      simpa [packedNormalizationSpaceBoundUpTo] using
        (packedNormalizationSuffixSpaceBound_le_polynomialSpaceBound
          periodicStrip packed column 0 periodicStrip.motif []
          (Nat.zero_le _) (by simp))
  | succ limit induction =>
      simp only [packedNormalizationSpaceBoundUpTo]
      apply Nat.max_le.mpr
      constructor
      · exact
          packedNormalizationSuffixSpaceBound_le_polynomialSpaceBound
            periodicStrip packed column (limit + 1)
            periodicStrip.motif [] limitBound (by simp)
      · exact induction (by omega)

theorem packedNormalizationSpaceBound_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationSpaceBound periodicStrip packed column ≤
      packedNormalizationPolynomialSpaceBound
        periodicStrip packed column := by
  exact
    packedNormalizationSpaceBoundUpTo_le_polynomialSpaceBound
      periodicStrip packed column
      (Encodable.encode periodicStrip.motif) (Nat.le_refl _)

/-- Typed suffix states reachable while the packed normalization countdown
is running. -/
def PackedNormalizationReachable
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (values : List Nat) : Prop :=
  ∃ valid remaining leading,
    values =
      Code.packedNormalizationState periodicStrip packed
        column valid remaining ∧
    countdown ≤ Encodable.encode periodicStrip.motif ∧
    periodicStrip.motif = leading ++ remaining

theorem packedNormalizationReachable_initial
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) :
    PackedNormalizationReachable periodicStrip packed column
      (Encodable.encode periodicStrip.motif)
      (Code.packedNormalizationState periodicStrip packed
        column valid periodicStrip.motif) := by
  exact ⟨valid, periodicStrip.motif, [], rfl,
    Nat.le_refl _, by simp⟩

theorem packedNormalizationReachable_step
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) (values : List Nat)
    (reachable :
      PackedNormalizationReachable periodicStrip packed column
        (countdown + 1) values) :
    PackedNormalizationReachable periodicStrip packed column
      countdown
      (Code.packedNormalizationNativeStep
        periodicStrip packed column values) := by
  obtain ⟨valid, remaining, leading, rfl,
    countdownBound, suffix⟩ := reachable
  cases remaining with
  | nil =>
      exact ⟨valid, [], leading,
        Code.packedNormalizationNativeStep_state_nil
          periodicStrip packed column valid,
        by omega, suffix⟩
  | cons cell remaining =>
      refine
        ⟨valid &&
            packed.normalizedAtBool periodicStrip column cell,
          remaining, leading ++ [cell], ?_, by omega, ?_⟩
      · exact
          Code.packedNormalizationNativeStep_state_cons
            periodicStrip packed column valid cell remaining
      · simpa [List.append_assoc] using suffix

theorem packedNormalizationReachable_iterate
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (countdown taken : Nat)
    (total :
      countdown + taken =
        Encodable.encode periodicStrip.motif) :
    PackedNormalizationReachable periodicStrip packed column
      countdown
      (((Code.packedNormalizationNativeStep
        periodicStrip packed column)^[taken])
        (Code.packedNormalizationState periodicStrip packed
          column valid periodicStrip.motif)) := by
  induction taken generalizing countdown with
  | zero =>
      have countdownEq :
          countdown = Encodable.encode periodicStrip.motif := by
        simpa using total
      subst countdown
      simpa using
        packedNormalizationReachable_initial
          periodicStrip packed column valid
  | succ taken induction =>
      have previousTotal :
          (countdown + 1) + taken =
            Encodable.encode periodicStrip.motif := by
        omega
      have previous := induction (countdown + 1) previousTotal
      rw [Function.iterate_succ_apply']
      exact
        packedNormalizationReachable_step periodicStrip packed
          column countdown _ previous

/-- The complete normalization countdown reuses one finite reachable-state
workspace envelope at every iteration. -/
theorem packedNormalizationFlatUniform
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    EvaluatorCodeFits
      (Code.flatIterate Code.packedNormalizationStepCode)
      (Encodable.encode periodicStrip.motif ::
        Code.packedNormalizationState periodicStrip packed
          column true periodicStrip.motif)
      (Code.packedNormalizationState periodicStrip packed column
        (packed.normalizedColumnBool periodicStrip column) [])
      (packedNormalizationSpaceBound
        periodicStrip packed column) where
  input_space := by
    have body :=
      packedNormalizationBody periodicStrip packed column
        (Encodable.encode periodicStrip.motif)
        true periodicStrip.motif
    exact body.input_space.trans
      (packedNormalizationBodyCost_le_spaceBound
        periodicStrip packed column
        (Encodable.encode periodicStrip.motif)
        true periodicStrip.motif []
        (Nat.le_refl _) (by simp))
  output_space := by
    let result :=
      packed.normalizedColumnBool periodicStrip column
    have body :=
      packedNormalizationBody periodicStrip packed column
        0 result []
    have input := body.input_space
    have cost :=
      packedNormalizationBodyCost_le_spaceBound
        periodicStrip packed column 0 result []
        periodicStrip.motif (Nat.zero_le _) (by simp)
    simp only [result] at input cost
    simp only [Code.packedNormalizationState,
      encodedListSpace_cons] at input ⊢
    omega
  call continuation bound budget after := by
    apply
      EvaluatorCallFits.flatIterate_of_reachable_code_fits
        (step :=
          Code.packedNormalizationNativeStep
            periodicStrip packed column)
        (bodyCost := fun _ _ =>
          packedNormalizationSpaceBound
            periodicStrip packed column)
        (invariant :=
          PackedNormalizationReachable
            periodicStrip packed column)
    · intro countdown values reachable
      obtain ⟨valid, remaining, leading, rfl,
        countdownBound, suffix⟩ := reachable
      exact
        (packedNormalizationBody periodicStrip packed column
          countdown valid remaining).mono
          (packedNormalizationBodyCost_le_spaceBound
            periodicStrip packed column countdown valid
            remaining leading countdownBound suffix)
    · exact packedNormalizationReachable_initial
        periodicStrip packed column true
    · exact packedNormalizationReachable_step
        periodicStrip packed column
    · intro countdown values reachable
      exact budget
    · rw [Code.packedNormalizationNativeStep_iterate,
        Code.packedNormalizationProcess_encode]
      simpa using after

def packedNormalizationColumnCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  let result :=
    Code.packedNormalizationState periodicStrip packed column
      (packed.normalizedColumnBool periodicStrip column) []
  getCost 6 result +
    (packedNormalizationSpaceBound periodicStrip packed column +
      packedNormalizationLoopInputCost
        periodicStrip packed column)

/-- Fitted closed program for normalization of one packed frontier column. -/
theorem packedNormalizationColumn
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    EvaluatorCodeFits Code.packedNormalizationColumnCode
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        column.val, packed.assignmentWord]
      [(packed.normalizedColumnBool
        periodicStrip column).toNat]
      (packedNormalizationColumnCost
        periodicStrip packed column) := by
  let result :=
    Code.packedNormalizationState periodicStrip packed column
      (packed.normalizedColumnBool periodicStrip column) []
  have loop :=
    comp
      (packedNormalizationFlatUniform
        periodicStrip packed column)
      (packedNormalizationLoopInput
        periodicStrip packed column)
  have projected := comp (get 6 result) loop
  simpa [Code.packedNormalizationColumnCode,
    packedNormalizationColumnCost, result,
    Code.packedNormalizationState] using projected

theorem packedNormalizationLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationLoopInputCost periodicStrip packed column ≤
      1000 *
        (encodedListSpace
          [4096 * (periodicStrip.period + packed.phase +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + packed.assignmentWord + 100) + 2000] +
          1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let limit :=
    4096 * (periodicStrip.period + packed.phase +
      motifCode + motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode +
      column.val + packed.assignmentWord + 100) + 2000
  let unit := encodedListSpace [limit] + 1
  change
    packedNormalizationLoopInputCost periodicStrip packed column ≤
      1000 * unit
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, encodedListSpace_cons,
      encodedListSpace_nil]
  have periodBits :=
    encodeNat_length_mono
      (show periodicStrip.period ≤ limit by
        simp only [limit]
        omega)
  have phaseBits :=
    encodeNat_length_mono
      (show packed.phase ≤ limit by
        simp only [limit]
        omega)
  have motifBits :=
    encodeNat_length_mono
      (show motifCode ≤ limit by
        simp only [limit]
        omega)
  have columnBits :=
    encodeNat_length_mono
      (show column.val ≤ limit by
        simp only [limit]
        omega)
  have wordBits :=
    encodeNat_length_mono
      (show packed.assignmentWord ≤ limit by
        simp only [limit]
        omega)
  have periodSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.period + 1 ≤ limit by
        simp only [limit]
        omega)
  have phaseSuccBits :=
    encodeNat_length_mono
      (show packed.phase + 1 ≤ limit by
        simp only [limit]
        omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have columnSuccBits :=
    encodeNat_length_mono
      (show column.val + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show packed.assignmentWord + 1 ≤ limit by
        simp only [limit]
        omega)
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
  simp [packedNormalizationLoopInputCost,
    prependCost, getCost, dropCost, headCost,
    idCost, nilCost, oneCost, zeroCost,
    tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    unitEq, zeroBits, oneBits]
  clear * - periodBits phaseBits motifBitsRaw columnBits wordBits
    periodSuccBits phaseSuccBits motifSuccBitsRaw
    columnSuccBits wordSuccBits unitEq
  omega

theorem packedNormalizationResultProjectionCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    getCost 6
        (Code.packedNormalizationState periodicStrip packed column
          (packed.normalizedColumnBool periodicStrip column) []) ≤
      100 *
        (encodedListSpace
          [4096 * (periodicStrip.period + packed.phase +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + packed.assignmentWord + 100) + 2000] +
          1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let limit :=
    4096 * (periodicStrip.period + packed.phase +
      motifCode + motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode +
      column.val + packed.assignmentWord + 100) + 2000
  let unit := encodedListSpace [limit] + 1
  change
    getCost 6
        (Code.packedNormalizationState periodicStrip packed column
          (packed.normalizedColumnBool periodicStrip column) []) ≤
      100 * unit
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, encodedListSpace_cons,
      encodedListSpace_nil]
  have periodBits :=
    encodeNat_length_mono
      (show periodicStrip.period ≤ limit by
        simp only [limit]
        omega)
  have phaseBits :=
    encodeNat_length_mono
      (show packed.phase ≤ limit by
        simp only [limit]
        omega)
  have motifBits :=
    encodeNat_length_mono
      (show motifCode ≤ limit by
        simp only [limit]
        omega)
  have columnBits :=
    encodeNat_length_mono
      (show column.val ≤ limit by
        simp only [limit]
        omega)
  have wordBits :=
    encodeNat_length_mono
      (show packed.assignmentWord ≤ limit by
        simp only [limit]
        omega)
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
  cases normalized :
      packed.normalizedColumnBool periodicStrip column <;>
    simp [Code.packedNormalizationState,
      getCost, dropCost, headCost, idCost,
      nilCost, tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq, zeroBits, oneBits, twoBits] <;>
    clear * - periodBits phaseBits motifBitsRaw columnBits wordBits
      unitEq <;>
    omega

private theorem packedNormalizationColumnBudget
    (unit projection space input : Nat)
    (projectionBound : projection ≤ 100 * unit)
    (spaceBound :
      space ≤ 1000000000000000000000000000000000 * unit)
    (inputBound : input ≤ 1000 * unit) :
    projection + (space + input) ≤
      2000000000000000000000000000000000 * unit := by
  omega

set_option maxHeartbeats 100000 in
theorem packedNormalizationColumnCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationColumnCost periodicStrip packed column ≤
      2000000000000000000000000000000000 *
        (encodedListSpace
          [4096 * (periodicStrip.period + packed.phase +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + packed.assignmentWord + 100) + 2000] +
          1) := by
  let motifCode := Encodable.encode periodicStrip.motif
  let limit :=
    4096 * (periodicStrip.period + packed.phase +
      motifCode + motifCode + motifCode + motifCode +
      motifCode + motifCode + motifCode +
      column.val + packed.assignmentWord + 100) + 2000
  let unit := encodedListSpace [limit] + 1
  change
    packedNormalizationColumnCost periodicStrip packed column ≤
      2000000000000000000000000000000000 * unit
  have spaceGlobal :
      packedNormalizationSpaceBound periodicStrip packed column ≤
        1000000000000000000000000000000000 * unit := by
    simpa [packedNormalizationPolynomialSpaceBound,
      motifCode, limit, unit] using
      packedNormalizationSpaceBound_le_polynomialSpaceBound
        periodicStrip packed column
  have inputGlobal :
      packedNormalizationLoopInputCost periodicStrip packed column ≤
        1000 * unit := by
    simpa [motifCode, limit, unit] using
      packedNormalizationLoopInputCost_le_linear
        periodicStrip packed column
  have projectionGlobal :
      getCost 6
          (Code.packedNormalizationState periodicStrip packed column
            (packed.normalizedColumnBool periodicStrip column) []) ≤
        100 * unit := by
    simpa [motifCode, limit, unit] using
      packedNormalizationResultProjectionCost_le_linear
        periodicStrip packed column
  simp only [packedNormalizationColumnCost]
  exact
    packedNormalizationColumnBudget unit _ _ _
      projectionGlobal spaceGlobal inputGlobal

end EvaluatorCodeFits

end PartrecToTM2
end Turing
