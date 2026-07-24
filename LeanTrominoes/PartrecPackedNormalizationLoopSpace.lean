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

/-- Sum of the exact body costs over every suffix of one motif, for a fixed
countdown.  This finite envelope is useful before its eventual polynomial
majorant is established. -/
def packedNormalizationSuffixSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (countdown : Nat) : List Cell → Nat
  | [] =>
      packedNormalizationBodyCost periodicStrip packed column
          countdown false [] +
        packedNormalizationBodyCost periodicStrip packed column
          countdown true []
  | cell :: remaining =>
      packedNormalizationBodyCost periodicStrip packed column
          countdown false (cell :: remaining) +
        packedNormalizationBodyCost periodicStrip packed column
          countdown true (cell :: remaining) +
        packedNormalizationSuffixSpaceBound periodicStrip packed
          column countdown remaining

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
      cases remaining <;>
        cases valid <;>
        simp [packedNormalizationSuffixSpaceBound] <;>
        omega
  | cons cell leading induction =>
      have bounded := induction
      simp only [List.cons_append,
        packedNormalizationSuffixSpaceBound]
      omega

/-- Sum of the suffix envelopes for every countdown up to the supplied
limit. -/
def packedNormalizationSpaceBoundUpTo
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    Nat → Nat
  | 0 =>
      packedNormalizationSuffixSpaceBound periodicStrip packed
        column 0 periodicStrip.motif
  | limit + 1 =>
      packedNormalizationSuffixSpaceBound periodicStrip packed
          column (limit + 1) periodicStrip.motif +
        packedNormalizationSpaceBoundUpTo periodicStrip packed
          column limit

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
        simp only [packedNormalizationSpaceBoundUpTo]
        omega

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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
