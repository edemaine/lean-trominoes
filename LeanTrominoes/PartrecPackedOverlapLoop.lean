/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecEncodedListDecode
import LeanTrominoes.PartrecPackedOverlapAt

/-!
# Streaming packed overlap over the shared frontier

For one of the four shared columns, the loop state is

`[motifCode, remainingCode, currentColumn, nextColumn,
  currentWord, nextWord, valid]`.

The second field streams through the encoded motif while the two packed
assignment words remain fixed.  Four copies of the completed column program
are then conjoined explicitly.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

def packedOverlapState
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (remaining : List Cell) : List Nat :=
  [Encodable.encode periodicStrip.motif,
    Encodable.encode remaining,
    column.succ.val, column.castSucc.val,
    current.assignmentWord, next.assignmentWord,
    valid.toNat]

/-- View the encoded motif suffix in state field one. -/
def packedOverlapViewCode : Code :=
  encodedListViewCode.comp (get 1)

def packedOverlapHeadCode : Code :=
  (get 1).comp packedOverlapViewCode

def packedOverlapTailCode : Code :=
  (get 2).comp packedOverlapViewCode

@[simp]
theorem packedOverlapViewCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (remaining : List Cell) :
    packedOverlapViewCode.eval
        (packedOverlapState periodicStrip current next
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
          simp [packedOverlapViewCode, packedOverlapState]
        _ = pure [0, 0, 0] :=
          encodedListViewCode_eval ([] : List Cell)
  | cons cell suffix =>
      calc
        _ = encodedListViewCode.eval
            [Encodable.encode (cell :: suffix)] := by
          simp [packedOverlapViewCode, packedOverlapState]
        _ = pure
            [1, Encodable.encode cell,
              Encodable.encode suffix] :=
          encodedListViewCode_eval (cell :: suffix)

@[simp]
theorem packedOverlapHeadCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapHeadCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure [Encodable.encode cell] := by
  simp [packedOverlapHeadCode]

@[simp]
theorem packedOverlapTailCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapTailCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure [Encodable.encode remaining] := by
  simp [packedOverlapTailCode]

/-- Assemble the one-occurrence comparison input from the streaming state. -/
def packedOverlapAtArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 2) <|
      prepend (get 3) <|
        prepend packedOverlapHeadCode <|
          prepend (get 4) (get 5)

@[simp]
theorem packedOverlapAtArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapAtArgumentsCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure
        (packedOverlapAtInput periodicStrip.motif
          column.succ.val column.castSucc.val cell
          current.assignmentWord next.assignmentWord) := by
  let state :=
    packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  have headEval :=
    packedOverlapHeadCode_eval periodicStrip current next
      column valid cell remaining
  simp only [packedOverlapAtArgumentsCode, Code.prepend_eval_eq]
  rw [show (get 0).eval state =
      pure [Encodable.encode periodicStrip.motif] by
    simp [state, packedOverlapState]]
  rw [show (get 2).eval state =
      pure [column.succ.val] by
    simp [state, packedOverlapState]]
  rw [show (get 3).eval state =
      pure [column.castSucc.val] by
    simp [state, packedOverlapState]]
  rw [headEval]
  rw [show (get 4).eval state =
      pure [current.assignmentWord] by
    simp [state, packedOverlapState]]
  rw [show (get 5).eval state =
      pure [next.assignmentWord] by
    simp [state, packedOverlapState]]
  simp [packedOverlapAtInput]

def packedOverlapHeadValidCode : Code :=
  packedOverlapAtCode.comp packedOverlapAtArgumentsCode

@[simp]
theorem packedOverlapHeadValidCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapHeadValidCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure
        [(current.overlapsAtBool periodicStrip
          next column cell).toNat] := by
  calc
    _ = packedOverlapAtCode.eval
        (packedOverlapAtInput periodicStrip.motif
          column.succ.val column.castSucc.val cell
          current.assignmentWord next.assignmentWord) := by
      simp [packedOverlapHeadValidCode]
    _ = _ := packedOverlapAtCode_eval_semantic
      periodicStrip current next column cell

def packedOverlapUpdatedValidCode : Code :=
  boolAnd (get 6) packedOverlapHeadValidCode

@[simp]
theorem packedOverlapUpdatedValidCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapUpdatedValidCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure
        [(valid &&
          current.overlapsAtBool periodicStrip next column cell).toNat] := by
  have combined :=
    boolAnd_eval_at (get 6) packedOverlapHeadValidCode
      (packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      valid.toNat
      (current.overlapsAtBool periodicStrip next column cell).toNat
      (by simp [packedOverlapState])
      (packedOverlapHeadValidCode_eval periodicStrip current next
        column valid cell remaining)
  cases valid <;>
    cases overlap :
      current.overlapsAtBool periodicStrip next column cell <;>
    simpa [packedOverlapUpdatedValidCode, overlap] using combined

/-- Consume one nonempty encoded motif suffix. -/
def packedOverlapConsStepCode : Code :=
  prepend (get 0) <|
    prepend packedOverlapTailCode <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend (get 4) <|
            prepend (get 5) packedOverlapUpdatedValidCode

@[simp]
theorem packedOverlapConsStepCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapConsStepCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure
        (packedOverlapState periodicStrip current next column
          (valid &&
            current.overlapsAtBool periodicStrip next column cell)
          remaining) := by
  let state :=
    packedOverlapState periodicStrip current next
      column valid (cell :: remaining)
  have tailEval :=
    packedOverlapTailCode_eval periodicStrip current next
      column valid cell remaining
  have updatedEval :=
    packedOverlapUpdatedValidCode_eval periodicStrip current next
      column valid cell remaining
  simp only [packedOverlapConsStepCode, Code.prepend_eval_eq]
  rw [show (get 0).eval state =
      pure [Encodable.encode periodicStrip.motif] by
    simp [state, packedOverlapState]]
  rw [tailEval]
  rw [show (get 2).eval state =
      pure [column.succ.val] by
    simp [state, packedOverlapState]]
  rw [show (get 3).eval state =
      pure [column.castSucc.val] by
    simp [state, packedOverlapState]]
  rw [show (get 4).eval state =
      pure [current.assignmentWord] by
    simp [state, packedOverlapState]]
  rw [show (get 5).eval state =
      pure [next.assignmentWord] by
    simp [state, packedOverlapState]]
  rw [updatedEval]
  simp [packedOverlapState]

/-- Empty suffixes are fixed points; nonempty suffixes consume one cell. -/
def packedOverlapStepCode : Code :=
  branchZero (get 1) id packedOverlapConsStepCode

@[simp]
theorem packedOverlapStepCode_eval_nil
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) :
    packedOverlapStepCode.eval
        (packedOverlapState periodicStrip current next
          column valid []) =
      pure
        (packedOverlapState periodicStrip current next
          column valid []) := by
  exact
    branchZero_eval_zero_at (get 1) id packedOverlapConsStepCode
      (packedOverlapState periodicStrip current next
        column valid [])
      0 (by simp [packedOverlapState])
      (packedOverlapState periodicStrip current next
        column valid [])
      (by simp) rfl

@[simp]
theorem packedOverlapStepCode_eval_cons
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapStepCode.eval
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      pure
        (packedOverlapState periodicStrip current next column
          (valid &&
            current.overlapsAtBool periodicStrip next column cell)
          remaining) := by
  exact
    branchZero_eval_succ_at (get 1) id packedOverlapConsStepCode
      (packedOverlapState periodicStrip current next
        column valid (cell :: remaining))
      (Encodable.encode (cell :: remaining))
      (by simp [packedOverlapState])
      (packedOverlapState periodicStrip current next column
        (valid &&
          current.overlapsAtBool periodicStrip next column cell)
        remaining)
      (packedOverlapConsStepCode_eval periodicStrip current next
        column valid cell remaining)
      (by simp)

/-- Total list semantics used by the evaluator-space loop rule. -/
def packedOverlapNativeStep
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (values : List Nat) : List Nat :=
  match
      (Encodable.decode (values[1]?.getD 0) :
        Option (List Cell)) with
  | none => values
  | some [] => values
  | some (cell :: remaining) =>
      [Encodable.encode periodicStrip.motif,
        Encodable.encode remaining,
        column.succ.val, column.castSucc.val,
        current.assignmentWord, next.assignmentWord,
        (decide (values[6]?.getD 0 ≠ 0) &&
          current.overlapsAtBool periodicStrip next column cell).toNat]

@[simp]
theorem packedOverlapNativeStep_state_nil
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) :
    packedOverlapNativeStep periodicStrip current next column
        (packedOverlapState periodicStrip current next
          column valid []) =
      packedOverlapState periodicStrip current next
        column valid [] := by
  simp [packedOverlapNativeStep, packedOverlapState]

@[simp]
theorem packedOverlapNativeStep_state_cons
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    packedOverlapNativeStep periodicStrip current next column
        (packedOverlapState periodicStrip current next
          column valid (cell :: remaining)) =
      packedOverlapState periodicStrip current next column
        (valid &&
          current.overlapsAtBool periodicStrip next column cell)
        remaining := by
  unfold packedOverlapNativeStep
  rw [show
    (Encodable.decode
        ((packedOverlapState periodicStrip current next column
          valid (cell :: remaining))[1]?.getD 0) :
      Option (List Cell)) =
        some (cell :: remaining) by
    change
      Encodable.decode (Encodable.encode (cell :: remaining)) =
        some (cell :: remaining)
    exact Encodable.encodek (cell :: remaining)]
  cases valid <;>
    cases overlap :
      current.overlapsAtBool periodicStrip next column cell <;>
    simp [packedOverlapState, overlap]

/-- Typed semantics of a fixed number of streaming motif steps. -/
def packedOverlapProcess
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    Nat → Bool → List Cell → List Nat
  | 0, valid, remaining =>
      packedOverlapState periodicStrip current next
        column valid remaining
  | steps + 1, valid, [] =>
      packedOverlapProcess periodicStrip current next
        column steps valid []
  | steps + 1, valid, cell :: remaining =>
      packedOverlapProcess periodicStrip current next
        column steps
        (valid &&
          current.overlapsAtBool periodicStrip next column cell)
        remaining

theorem packedOverlapNativeStep_iterate
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (steps : Nat) (valid : Bool) (remaining : List Cell) :
    ((packedOverlapNativeStep
      periodicStrip current next column)^[steps])
        (packedOverlapState periodicStrip current next
          column valid remaining) =
      packedOverlapProcess periodicStrip current next
        column steps valid remaining := by
  induction steps generalizing valid remaining with
  | zero =>
      rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      cases remaining with
      | nil =>
          rw [packedOverlapNativeStep_state_nil]
          simpa [packedOverlapProcess] using induction valid []
      | cons cell remaining =>
          rw [packedOverlapNativeStep_state_cons]
          simpa [packedOverlapProcess] using
            induction
              (valid &&
                current.overlapsAtBool periodicStrip next column cell)
              remaining

theorem packedOverlapFlatIterateCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (steps : Nat) (valid : Bool) (remaining : List Cell) :
    (flatIterate packedOverlapStepCode).eval
        (steps ::
          packedOverlapState periodicStrip current next
            column valid remaining) =
      pure
        (packedOverlapProcess periodicStrip current next
          column steps valid remaining) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing valid remaining with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval, packedOverlapProcess]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      cases remaining with
      | nil =>
          refine
            ⟨steps ::
                packedOverlapState periodicStrip current next
                  column valid [],
              ?_, ?_⟩
          · simp [flatCountdownBody,
              packedOverlapStepCode_eval_nil]
          · simpa [packedOverlapProcess] using induction valid []
      | cons cell remaining =>
          let nextValid :=
            valid &&
              current.overlapsAtBool periodicStrip next column cell
          refine
            ⟨steps ::
                packedOverlapState periodicStrip current next
                  column nextValid remaining,
              ?_, ?_⟩
          · simp [flatCountdownBody,
              packedOverlapStepCode_eval_cons, nextValid]
          · simpa [packedOverlapProcess, nextValid] using
              induction nextValid remaining

theorem packedOverlapProcess_of_length_le
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (steps : Nat) (valid : Bool) (remaining : List Cell)
    (enough : remaining.length ≤ steps) :
    packedOverlapProcess periodicStrip current next column
        steps valid remaining =
      packedOverlapState periodicStrip current next column
        (valid &&
          remaining.all fun cell =>
            current.overlapsAtBool periodicStrip next column cell)
        [] := by
  induction remaining generalizing steps valid with
  | nil =>
      induction steps generalizing valid with
      | zero =>
          simp [packedOverlapProcess, packedOverlapState]
      | succ steps induction =>
          simpa [packedOverlapProcess] using induction valid
  | cons cell remaining induction =>
      cases steps with
      | zero =>
          simp at enough
      | succ steps =>
          have remainingEnough : remaining.length ≤ steps := by
            simpa using enough
          rw [packedOverlapProcess]
          rw [induction steps
            (valid &&
              current.overlapsAtBool periodicStrip next column cell)
            remainingEnough]
          simp [packedOverlapState, Bool.and_assoc]

theorem packedOverlapProcess_encode
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4)
    (valid : Bool) :
    packedOverlapProcess periodicStrip current next column
        (Encodable.encode periodicStrip.motif)
        valid periodicStrip.motif =
      packedOverlapState periodicStrip current next column
        (valid &&
          current.overlapsColumnBool periodicStrip next column)
        [] := by
  simpa [PackedWindowState.overlapsColumnBool] using
    packedOverlapProcess_of_length_le periodicStrip current next
      column (Encodable.encode periodicStrip.motif)
      valid periodicStrip.motif
      (length_le_encode periodicStrip.motif)

/-- Assemble the countdown and initial state from
`[motifCode, currentColumn, nextColumn, currentWord, nextWord]`. -/
def packedOverlapLoopInputCode : Code :=
  prepend (get 0) <|
    prepend (get 0) <|
      prepend (get 0) <|
        prepend (get 1) <|
          prepend (get 2) <|
            prepend (get 3) <|
              prepend (get 4) one

@[simp]
theorem packedOverlapLoopInputCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapLoopInputCode.eval
        [Encodable.encode periodicStrip.motif,
          column.val + 1, column.val,
          current.assignmentWord, next.assignmentWord] =
      pure
        (Encodable.encode periodicStrip.motif ::
          packedOverlapState periodicStrip current next
            column true periodicStrip.motif) := by
  simp [packedOverlapLoopInputCode, packedOverlapState]

/-- Scan one complete motif column and project its overlap tag. -/
def packedOverlapColumnCode : Code :=
  (get 6).comp <|
    (flatIterate packedOverlapStepCode).comp
      packedOverlapLoopInputCode

@[simp]
theorem packedOverlapColumnCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    packedOverlapColumnCode.eval
        [Encodable.encode periodicStrip.motif,
          column.val + 1, column.val,
          current.assignmentWord, next.assignmentWord] =
      pure
        [(current.overlapsColumnBool periodicStrip
          next column).toNat] := by
  let values :=
    [Encodable.encode periodicStrip.motif,
      column.val + 1, column.val,
      current.assignmentWord, next.assignmentWord]
  have inputRun :=
    packedOverlapLoopInputCode_eval periodicStrip current next column
  have loopRun :=
    packedOverlapFlatIterateCode_eval periodicStrip current next column
      (Encodable.encode periodicStrip.motif)
      true periodicStrip.motif
  rw [packedOverlapProcess_encode] at loopRun
  have composed :
      ((flatIterate packedOverlapStepCode).comp
          packedOverlapLoopInputCode).eval values =
        pure
          (packedOverlapState periodicStrip current next column
            (current.overlapsColumnBool periodicStrip next column)
            []) := by
    rw [ToPartrec.Code.comp_eval]
    change
      (packedOverlapLoopInputCode.eval values).bind
          (flatIterate packedOverlapStepCode).eval =
        _
    rw [inputRun]
    simpa using loopRun
  change packedOverlapColumnCode.eval values = _
  calc
    _ = (get 6).eval
        (packedOverlapState periodicStrip current next column
          (current.overlapsColumnBool periodicStrip next column)
          []) := by
      simp [packedOverlapColumnCode, composed]
    _ = _ := by simp [packedOverlapState]

/-- Fixed-column input assembly from `[motifCode, currentWord, nextWord]`. -/
def packedOverlapColumnArgumentsCode (column : Fin 4) : Code :=
  prepend (get 0) <|
    prepend (numeral column.succ.val) <|
      prepend (numeral column.castSucc.val) <|
        prepend (get 1) (get 2)

@[simp]
theorem packedOverlapColumnArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    (packedOverlapColumnArgumentsCode column).eval
        [Encodable.encode periodicStrip.motif,
          current.assignmentWord, next.assignmentWord] =
      pure
        [Encodable.encode periodicStrip.motif,
          column.val + 1, column.val,
          current.assignmentWord, next.assignmentWord] := by
  simp [packedOverlapColumnArgumentsCode, numeral]

def packedOverlapColumnAtCode (column : Fin 4) : Code :=
  packedOverlapColumnCode.comp
    (packedOverlapColumnArgumentsCode column)

@[simp]
theorem packedOverlapColumnAtCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (column : Fin 4) :
    (packedOverlapColumnAtCode column).eval
        [Encodable.encode periodicStrip.motif,
          current.assignmentWord, next.assignmentWord] =
      pure
        [(current.overlapsColumnBool periodicStrip
          next column).toNat] := by
  calc
    _ = packedOverlapColumnCode.eval
        [Encodable.encode periodicStrip.motif,
          column.val + 1, column.val,
          current.assignmentWord, next.assignmentWord] := by
      simp [packedOverlapColumnAtCode]
    _ = _ := packedOverlapColumnCode_eval
      periodicStrip current next column

private theorem boolAnd_bool_eval_at
    (left right : Code) (values : List Nat)
    (leftValue rightValue : Bool)
    (leftCorrect :
      left.eval values = pure [leftValue.toNat])
    (rightCorrect :
      right.eval values = pure [rightValue.toNat]) :
    (boolAnd left right).eval values =
      pure [(leftValue && rightValue).toNat] := by
  have combined :=
    boolAnd_eval_at left right values
      leftValue.toNat rightValue.toNat
      leftCorrect rightCorrect
  cases leftValue <;> cases rightValue <;> simpa using combined

/-- Conjoin the four shared-column scans. -/
def packedOverlapColumnsCode : Code :=
  boolAnd (packedOverlapColumnAtCode (0 : Fin 4)) <|
    boolAnd (packedOverlapColumnAtCode (1 : Fin 4)) <|
      boolAnd (packedOverlapColumnAtCode (2 : Fin 4))
        (packedOverlapColumnAtCode (3 : Fin 4))

@[simp]
theorem packedOverlapColumnsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedOverlapColumnsCode.eval
        [Encodable.encode periodicStrip.motif,
          current.assignmentWord, next.assignmentWord] =
      pure
        [((List.finRange 4).all fun column =>
          current.overlapsColumnBool periodicStrip next column).toNat] := by
  let values :=
    [Encodable.encode periodicStrip.motif,
      current.assignmentWord, next.assignmentWord]
  have third :=
    boolAnd_bool_eval_at
      (packedOverlapColumnAtCode (2 : Fin 4))
      (packedOverlapColumnAtCode (3 : Fin 4))
      values
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4))
      (current.overlapsColumnBool periodicStrip next (3 : Fin 4))
      (packedOverlapColumnAtCode_eval periodicStrip current next 2)
      (packedOverlapColumnAtCode_eval periodicStrip current next 3)
  have second :=
    boolAnd_bool_eval_at
      (packedOverlapColumnAtCode (1 : Fin 4))
      (boolAnd (packedOverlapColumnAtCode (2 : Fin 4))
        (packedOverlapColumnAtCode (3 : Fin 4)))
      values
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4))
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool periodicStrip next (3 : Fin 4))
      (packedOverlapColumnAtCode_eval periodicStrip current next 1)
      third
  have first :=
    boolAnd_bool_eval_at
      (packedOverlapColumnAtCode (0 : Fin 4))
      (boolAnd (packedOverlapColumnAtCode (1 : Fin 4)) <|
        boolAnd (packedOverlapColumnAtCode (2 : Fin 4))
          (packedOverlapColumnAtCode (3 : Fin 4)))
      values
      (current.overlapsColumnBool periodicStrip next (0 : Fin 4))
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
        (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
          current.overlapsColumnBool periodicStrip next (3 : Fin 4)))
      (packedOverlapColumnAtCode_eval periodicStrip current next 0)
      second
  simpa [packedOverlapColumnsCode, values,
    List.finRange_succ] using first

end Turing.ToPartrec.Code
