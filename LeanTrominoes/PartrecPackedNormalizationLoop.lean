import LeanTrominoes.PartrecEncodedListDecode
import LeanTrominoes.PartrecPackedNormalizedAt

/-!
# Streaming packed normalization over one motif column

The loop state is

`[motifCode, remainingCode, period, phase, column, word, valid]`.

The original motif code is retained for each packed assignment lookup, while
the second field streams through an encoded suffix.  The original motif code
also serves as a safe numeric countdown.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

def packedNormalizationState
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (remaining : List Cell) : List Nat :=
  [Encodable.encode periodicStrip.motif,
    Encodable.encode remaining, periodicStrip.period,
    packed.phase, column.val, packed.assignmentWord,
    valid.toNat]

/-- View the encoded suffix in state field one. -/
def packedNormalizationViewCode : Code :=
  encodedListViewCode.comp (get 1)

def packedNormalizationHeadCode : Code :=
  (get 1).comp packedNormalizationViewCode

def packedNormalizationTailCode : Code :=
  (get 2).comp packedNormalizationViewCode

@[simp]
theorem packedNormalizationViewCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (remaining : List Cell) :
    packedNormalizationViewCode.eval
        (packedNormalizationState periodicStrip packed
          column valid remaining) =
      pure
        (match remaining with
        | [] => [0, 0, 0]
        | cell :: suffix =>
            [1, Encodable.encode cell,
              Encodable.encode suffix]) := by
  cases remaining with
  | nil =>
      calc
        _ = encodedListViewCode.eval [0] := by
          simp [packedNormalizationViewCode,
            packedNormalizationState]
        _ = pure [0, 0, 0] :=
          encodedListViewCode_eval ([] : List Cell)
  | cons cell suffix =>
      calc
        _ = encodedListViewCode.eval
            [Encodable.encode (cell :: suffix)] := by
          simp [packedNormalizationViewCode,
            packedNormalizationState]
        _ = pure
            [1, Encodable.encode cell,
              Encodable.encode suffix] :=
          encodedListViewCode_eval (cell :: suffix)

@[simp]
theorem packedNormalizationHeadCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationHeadCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure [Encodable.encode cell] := by
  simp [packedNormalizationHeadCode]

@[simp]
theorem packedNormalizationTailCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationTailCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure [Encodable.encode remaining] := by
  simp [packedNormalizationTailCode]

/-- Assemble the one-cell predicate input from the streaming state. -/
def packedNormalizationAtArgumentsCode : Code :=
  prepend (get 2) <|
    prepend (get 3) <|
      prepend (get 0) <|
        prepend (get 4) <|
          prepend packedNormalizationHeadCode (get 5)

@[simp]
theorem packedNormalizationAtArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationAtArgumentsCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif, column.val,
          Encodable.encode cell, packed.assignmentWord] := by
  let state :=
    packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  have headEval :=
    packedNormalizationHeadCode_eval
      periodicStrip packed column valid cell remaining
  simp only [packedNormalizationAtArgumentsCode,
    Code.prepend_eval_eq]
  rw [show (get 2).eval state =
      pure [periodicStrip.period] by
    simp [state, packedNormalizationState]]
  rw [show (get 3).eval state =
      pure [packed.phase] by
    simp [state, packedNormalizationState]]
  rw [show (get 0).eval state =
      pure [Encodable.encode periodicStrip.motif] by
    simp [state, packedNormalizationState]]
  rw [show (get 4).eval state =
      pure [column.val] by
    simp [state, packedNormalizationState]]
  rw [headEval]
  rw [show (get 5).eval state =
      pure [packed.assignmentWord] by
    simp [state, packedNormalizationState]]
  simp

def packedNormalizationHeadValidCode : Code :=
  packedNormalizedAtCode.comp
    packedNormalizationAtArgumentsCode

@[simp]
theorem packedNormalizationHeadValidCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationHeadValidCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure
        [(packed.normalizedAtBool periodicStrip
          column cell).toNat] := by
  have arguments :=
    packedNormalizationAtArgumentsCode_eval
      periodicStrip packed column valid cell remaining
  simp [packedNormalizationHeadValidCode, arguments,
    packedNormalizedAtResult_eq_semantic]

def packedNormalizationUpdatedValidCode : Code :=
  boolAnd (get 6) packedNormalizationHeadValidCode

@[simp]
theorem packedNormalizationUpdatedValidCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationUpdatedValidCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure
        [(valid &&
          packed.normalizedAtBool periodicStrip column cell).toNat] := by
  have combined :=
    boolAnd_eval_at (get 6)
      packedNormalizationHeadValidCode
      (packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      valid.toNat
      (packed.normalizedAtBool periodicStrip column cell).toNat
      (by simp [packedNormalizationState])
      (packedNormalizationHeadValidCode_eval
        periodicStrip packed column valid cell remaining)
  cases valid <;>
    cases normalized :
      packed.normalizedAtBool periodicStrip column cell <;>
    simpa [packedNormalizationUpdatedValidCode,
      normalized] using combined

/-- Consume one nonempty encoded motif suffix. -/
def packedNormalizationConsStepCode : Code :=
  prepend (get 0) <|
    prepend packedNormalizationTailCode <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend (get 4) <|
            prepend (get 5)
              packedNormalizationUpdatedValidCode

@[simp]
theorem packedNormalizationConsStepCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationConsStepCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure
        (packedNormalizationState periodicStrip packed column
          (valid &&
            packed.normalizedAtBool periodicStrip column cell)
          remaining) := by
  let state :=
    packedNormalizationState periodicStrip packed
      column valid (cell :: remaining)
  have tailEval :=
    packedNormalizationTailCode_eval
      periodicStrip packed column valid cell remaining
  have updatedEval :=
    packedNormalizationUpdatedValidCode_eval
      periodicStrip packed column valid cell remaining
  simp only [packedNormalizationConsStepCode,
    Code.prepend_eval_eq]
  rw [show (get 0).eval state =
      pure [Encodable.encode periodicStrip.motif] by
    simp [state, packedNormalizationState]]
  rw [tailEval]
  rw [show (get 2).eval state =
      pure [periodicStrip.period] by
    simp [state, packedNormalizationState]]
  rw [show (get 3).eval state =
      pure [packed.phase] by
    simp [state, packedNormalizationState]]
  rw [show (get 4).eval state =
      pure [column.val] by
    simp [state, packedNormalizationState]]
  rw [show (get 5).eval state =
      pure [packed.assignmentWord] by
    simp [state, packedNormalizationState]]
  rw [updatedEval]
  simp [packedNormalizationState]

/-- Empty suffixes are fixed points; nonempty suffixes consume one cell. -/
def packedNormalizationStepCode : Code :=
  branchZero (get 1) id packedNormalizationConsStepCode

@[simp]
theorem packedNormalizationStepCode_eval_nil
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) :
    packedNormalizationStepCode.eval
        (packedNormalizationState periodicStrip packed
          column valid []) =
      pure
        (packedNormalizationState periodicStrip packed
          column valid []) := by
  exact
    branchZero_eval_zero_at (get 1) id
      packedNormalizationConsStepCode
      (packedNormalizationState periodicStrip packed
        column valid [])
      0 (by simp [packedNormalizationState])
      (packedNormalizationState periodicStrip packed
        column valid [])
      (by simp) rfl

@[simp]
theorem packedNormalizationStepCode_eval_cons
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationStepCode.eval
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      pure
        (packedNormalizationState periodicStrip packed column
          (valid &&
            packed.normalizedAtBool periodicStrip column cell)
          remaining) := by
  exact
    branchZero_eval_succ_at (get 1) id
      packedNormalizationConsStepCode
      (packedNormalizationState periodicStrip packed
        column valid (cell :: remaining))
      (Encodable.encode (cell :: remaining))
      (by simp [packedNormalizationState])
      (packedNormalizationState periodicStrip packed column
        (valid &&
          packed.normalizedAtBool periodicStrip column cell)
        remaining)
      (packedNormalizationConsStepCode_eval
        periodicStrip packed column valid cell remaining)
      (by simp)

/-- Total list semantics used by the evaluator-space loop rule.  Only typed
suffix states are reachable from the fitted initial state. -/
def packedNormalizationNativeStep
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (values : List Nat) : List Nat :=
  match
      (Encodable.decode (values[1]?.getD 0) :
        Option (List Cell)) with
  | none => values
  | some [] => values
  | some (cell :: remaining) =>
      [Encodable.encode periodicStrip.motif,
        Encodable.encode remaining, periodicStrip.period,
        packed.phase, column.val, packed.assignmentWord,
        (decide (values[6]?.getD 0 ≠ 0) &&
          packed.normalizedAtBool periodicStrip column cell).toNat]

@[simp]
theorem packedNormalizationNativeStep_state_nil
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) :
    packedNormalizationNativeStep periodicStrip packed column
        (packedNormalizationState periodicStrip packed
          column valid []) =
      packedNormalizationState periodicStrip packed
        column valid [] := by
  simp [packedNormalizationNativeStep,
    packedNormalizationState]

@[simp]
theorem packedNormalizationNativeStep_state_cons
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedNormalizationNativeStep periodicStrip packed column
        (packedNormalizationState periodicStrip packed
          column valid (cell :: remaining)) =
      packedNormalizationState periodicStrip packed column
        (valid &&
          packed.normalizedAtBool periodicStrip column cell)
        remaining := by
  unfold packedNormalizationNativeStep
  rw [show
    (Encodable.decode
        ((packedNormalizationState periodicStrip packed column
          valid (cell :: remaining))[1]?.getD 0) :
      Option (List Cell)) =
        some (cell :: remaining) by
    change
      Encodable.decode (Encodable.encode (cell :: remaining)) =
        some (cell :: remaining)
    exact Encodable.encodek (cell :: remaining)]
  cases valid <;>
    cases normalized :
      packed.normalizedAtBool periodicStrip column cell <;>
    simp [packedNormalizationState, normalized]

/-- Typed semantics of a fixed number of streaming suffix steps. -/
def packedNormalizationProcess
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    Nat → Bool → List Cell → List Nat
  | 0, valid, remaining =>
      packedNormalizationState periodicStrip packed
        column valid remaining
  | steps + 1, valid, [] =>
      packedNormalizationProcess periodicStrip packed column
        steps valid []
  | steps + 1, valid, cell :: remaining =>
      packedNormalizationProcess periodicStrip packed column
        steps
        (valid &&
          packed.normalizedAtBool periodicStrip column cell)
        remaining

theorem packedNormalizationNativeStep_iterate
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (steps : Nat) (valid : Bool) (remaining : List Cell) :
    ((packedNormalizationNativeStep
      periodicStrip packed column)^[steps])
        (packedNormalizationState periodicStrip packed
          column valid remaining) =
      packedNormalizationProcess periodicStrip packed
        column steps valid remaining := by
  induction steps generalizing valid remaining with
  | zero =>
      rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      cases remaining with
      | nil =>
          rw [packedNormalizationNativeStep_state_nil]
          simpa [packedNormalizationProcess] using
            induction valid []
      | cons cell remaining =>
          rw [packedNormalizationNativeStep_state_cons]
          simpa [packedNormalizationProcess] using
            induction
              (valid &&
                packed.normalizedAtBool periodicStrip column cell)
              remaining

theorem packedNormalizationFlatIterateCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (steps : Nat) (valid : Bool) (remaining : List Cell) :
    (flatIterate packedNormalizationStepCode).eval
        (steps ::
          packedNormalizationState periodicStrip packed
            column valid remaining) =
      pure
        (packedNormalizationProcess periodicStrip packed
          column steps valid remaining) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing valid remaining with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval,
        packedNormalizationProcess]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      cases remaining with
      | nil =>
          refine
            ⟨steps ::
                packedNormalizationState periodicStrip packed
                  column valid [],
              ?_, ?_⟩
          · simp [flatCountdownBody,
              packedNormalizationStepCode_eval_nil]
          · simpa [packedNormalizationProcess] using
              induction valid []
      | cons cell remaining =>
          let nextValid :=
            valid &&
              packed.normalizedAtBool periodicStrip column cell
          refine
            ⟨steps ::
                packedNormalizationState periodicStrip packed
                  column nextValid remaining,
              ?_, ?_⟩
          · simp [flatCountdownBody,
              packedNormalizationStepCode_eval_cons,
              nextValid]
          · simpa [packedNormalizationProcess, nextValid] using
              induction nextValid remaining

theorem packedNormalizationProcess_of_length_le
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (steps : Nat) (valid : Bool) (remaining : List Cell)
    (enough : remaining.length ≤ steps) :
    packedNormalizationProcess periodicStrip packed column
        steps valid remaining =
      packedNormalizationState periodicStrip packed column
        (valid &&
          remaining.all fun cell =>
            packed.normalizedAtBool periodicStrip column cell)
        [] := by
  induction remaining generalizing steps valid with
  | nil =>
      induction steps generalizing valid with
      | zero =>
          simp [packedNormalizationProcess,
            packedNormalizationState]
      | succ steps induction =>
          simpa [packedNormalizationProcess] using
            induction valid
  | cons cell remaining induction =>
      cases steps with
      | zero =>
          simp at enough
      | succ steps =>
          have remainingEnough :
              remaining.length ≤ steps := by
            simpa using enough
          rw [packedNormalizationProcess]
          rw [induction steps
            (valid &&
              packed.normalizedAtBool periodicStrip column cell)
            remainingEnough]
          simp [packedNormalizationState, Bool.and_assoc]

theorem packedNormalizationProcess_encode
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (valid : Bool) :
    packedNormalizationProcess periodicStrip packed column
        (Encodable.encode periodicStrip.motif)
        valid periodicStrip.motif =
      packedNormalizationState periodicStrip packed column
        (valid &&
          packed.normalizedColumnBool periodicStrip column)
        [] := by
  simpa [PackedWindowState.normalizedColumnBool] using
    packedNormalizationProcess_of_length_le
      periodicStrip packed column
      (Encodable.encode periodicStrip.motif)
      valid periodicStrip.motif
      (length_le_encode periodicStrip.motif)

/-- Assemble the countdown and initial streaming state from
`[period, phase, motifCode, column, word]`. -/
def packedNormalizationLoopInputCode : Code :=
  prepend (get 2) <|
    prepend (get 2) <|
      prepend (get 2) <|
        prepend (get 0) <|
          prepend (get 1) <|
            prepend (get 3) <|
              prepend (get 4) one

@[simp]
theorem packedNormalizationLoopInputCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationLoopInputCode.eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          column.val, packed.assignmentWord] =
      pure
        (Encodable.encode periodicStrip.motif ::
          packedNormalizationState periodicStrip packed
            column true periodicStrip.motif) := by
  simp [packedNormalizationLoopInputCode,
    packedNormalizationState]

/-- Scan one complete motif column and project its normalization tag. -/
def packedNormalizationColumnCode : Code :=
  (get 6).comp <|
    (flatIterate packedNormalizationStepCode).comp
      packedNormalizationLoopInputCode

@[simp]
theorem packedNormalizationColumnCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationColumnCode.eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          column.val, packed.assignmentWord] =
      pure
        [(packed.normalizedColumnBool periodicStrip column).toNat] := by
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      column.val, packed.assignmentWord]
  have inputRun :=
    packedNormalizationLoopInputCode_eval
      periodicStrip packed column
  have loopRun :=
    packedNormalizationFlatIterateCode_eval
      periodicStrip packed column
      (Encodable.encode periodicStrip.motif)
      true periodicStrip.motif
  rw [packedNormalizationProcess_encode] at loopRun
  have composed :
      ((flatIterate packedNormalizationStepCode).comp
          packedNormalizationLoopInputCode).eval values =
        pure
          (packedNormalizationState periodicStrip packed column
            (packed.normalizedColumnBool periodicStrip column)
            []) := by
    calc
      _ = (flatIterate packedNormalizationStepCode).eval
          (Encodable.encode periodicStrip.motif ::
            packedNormalizationState periodicStrip packed
              column true periodicStrip.motif) := by
        simp [inputRun, values]
      _ = _ := by simpa using loopRun
  calc
    _ = (get 6).eval
        (packedNormalizationState periodicStrip packed column
          (packed.normalizedColumnBool periodicStrip column)
          []) := by
      simp [packedNormalizationColumnCode, composed, values]
    _ = _ := by simp [packedNormalizationState]

end Turing.ToPartrec.Code
