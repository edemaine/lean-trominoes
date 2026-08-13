/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPackedCenterBase
import LeanTrominoes.PartrecPackedNormalizationLoop
import LeanTrominoes.PartrecUnpair

/-!
# Streaming packed center validity over the motif

The one-base center checker is streamed over the encoded motif while retaining
only an encoded suffix and a Boolean accumulator.  The state reuses the seven
fields of the normalization loop, with its column field fixed to the center
column:

`[motifCode, remainingCode, period, phase, center, word, valid]`.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Typed center-loop state, represented in the same layout as a fixed-column
normalization state. -/
def packedCenterState
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (remaining : List Cell) : List Nat :=
  packedNormalizationState periodicStrip packed
    WindowState.center valid remaining

/-- Decode the encoded row component of the current motif head. -/
def packedCenterHeadRowCode : Code :=
  (get 1).comp (unpairCode.comp packedNormalizationHeadCode)

@[simp]
theorem packedCenterHeadRowCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    packedCenterHeadRowCode.eval
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      pure [Encodable.encode cell.2] := by
  rcases cell with ⟨x, y⟩
  simp [packedCenterHeadRowCode, packedCenterState,
    packedNormalizationHeadCode]

/-- Assemble the six-field one-base input from the streaming state. -/
def packedCenterBaseArgumentsCode : Code :=
  prepend (get 2) <|
    prepend (get 3) <|
      prepend (get 0) <|
        prepend packedNormalizationHeadCode <|
          prepend packedCenterHeadRowCode (get 5)

@[simp]
theorem packedCenterBaseArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    packedCenterBaseArgumentsCode.eval
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      pure [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        Encodable.encode cell, Encodable.encode cell.2,
        packed.assignmentWord] := by
  let state := packedCenterState periodicStrip packed valid
    (cell :: remaining)
  have headEval := packedNormalizationHeadCode_eval
    periodicStrip packed WindowState.center valid cell remaining
  have rowEval := packedCenterHeadRowCode_eval
    periodicStrip packed valid cell remaining
  simp only [packedCenterBaseArgumentsCode, Code.prepend_eval_eq]
  rw [show (get 2).eval state = pure [periodicStrip.period] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show (get 3).eval state = pure [packed.phase] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show (get 0).eval state =
      pure [Encodable.encode periodicStrip.motif] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show packedNormalizationHeadCode.eval state =
      pure [Encodable.encode cell] by
    exact headEval]
  rw [show packedCenterHeadRowCode.eval state =
      pure [Encodable.encode cell.2] by
    exact rowEval]
  rw [show (get 5).eval state = pure [packed.assignmentWord] by
    simp [state, packedCenterState, packedNormalizationState]]
  simp

/-- Check both center conditions at the current motif head. -/
def packedCenterHeadValidCode (tromino : Tromino) : Code :=
  (packedCenterBaseValidCode tromino).comp
    packedCenterBaseArgumentsCode

@[simp]
theorem packedCenterHeadValidCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    (packedCenterHeadValidCode tromino).eval
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      pure [((packed.centerBaseInsideBool
          tromino periodicStrip cell) &&
        packed.centerBaseCoveredBool
          tromino periodicStrip cell).toNat] := by
  have arguments := packedCenterBaseArgumentsCode_eval
    periodicStrip packed valid cell remaining
  have baseRun := packedCenterBaseValidCode_eval_semantic
    tromino periodicStrip wellFormed packed cell
  simpa only [packedCenterHeadValidCode] using
    (comp_eval_pure _ _ _ _ arguments).trans baseRun

/-- Conjoin the current head result with the loop accumulator. -/
def packedCenterUpdatedValidCode (tromino : Tromino) : Code :=
  boolAnd (get 6) (packedCenterHeadValidCode tromino)

@[simp]
theorem packedCenterUpdatedValidCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    (packedCenterUpdatedValidCode tromino).eval
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      pure [(valid &&
        (packed.centerBaseInsideBool tromino periodicStrip cell &&
          packed.centerBaseCoveredBool
            tromino periodicStrip cell)).toNat] := by
  have combined := boolAnd_eval_at (get 6)
    (packedCenterHeadValidCode tromino)
    (packedCenterState periodicStrip packed valid
      (cell :: remaining))
    valid.toNat
    ((packed.centerBaseInsideBool tromino periodicStrip cell &&
      packed.centerBaseCoveredBool
        tromino periodicStrip cell).toNat)
    (by simp [packedCenterState, packedNormalizationState])
    (packedCenterHeadValidCode_eval tromino periodicStrip
      wellFormed packed valid cell remaining)
  cases valid <;>
    cases inside :
      packed.centerBaseInsideBool tromino periodicStrip cell <;>
    cases covered :
      packed.centerBaseCoveredBool tromino periodicStrip cell <;>
    simpa [packedCenterUpdatedValidCode,
      inside, covered] using combined

/-- Consume one nonempty encoded motif suffix. -/
def packedCenterConsStepCode (tromino : Tromino) : Code :=
  prepend (get 0) <|
    prepend packedNormalizationTailCode <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend (get 4) <|
            prepend (get 5)
              (packedCenterUpdatedValidCode tromino)

@[simp]
theorem packedCenterConsStepCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    (packedCenterConsStepCode tromino).eval
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      pure (packedCenterState periodicStrip packed
        (valid &&
          (packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool
              tromino periodicStrip cell)) remaining) := by
  let state := packedCenterState periodicStrip packed valid
    (cell :: remaining)
  have tailEval := packedNormalizationTailCode_eval
    periodicStrip packed WindowState.center valid cell remaining
  have updatedEval := packedCenterUpdatedValidCode_eval
    tromino periodicStrip wellFormed packed valid cell remaining
  simp only [packedCenterConsStepCode, Code.prepend_eval_eq]
  rw [show (get 0).eval state =
      pure [Encodable.encode periodicStrip.motif] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show packedNormalizationTailCode.eval state =
      pure [Encodable.encode remaining] by
    exact tailEval]
  rw [show (get 2).eval state = pure [periodicStrip.period] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show (get 3).eval state = pure [packed.phase] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show (get 4).eval state = pure [WindowState.center.val] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show (get 5).eval state = pure [packed.assignmentWord] by
    simp [state, packedCenterState, packedNormalizationState]]
  rw [show (packedCenterUpdatedValidCode tromino).eval state =
      pure [(valid &&
        (packed.centerBaseInsideBool tromino periodicStrip cell &&
          packed.centerBaseCoveredBool
            tromino periodicStrip cell)).toNat] by
    simpa [state] using updatedEval]
  simp [packedCenterState, packedNormalizationState]

/-- Empty suffixes are fixed points; nonempty suffixes consume one cell. -/
def packedCenterStepCode (tromino : Tromino) : Code :=
  branchZero (get 1) id (packedCenterConsStepCode tromino)

@[simp]
theorem packedCenterStepCode_eval_nil
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool) :
    (packedCenterStepCode tromino).eval
        (packedCenterState periodicStrip packed valid []) =
      pure (packedCenterState periodicStrip packed valid []) := by
  exact branchZero_eval_zero_at (get 1) id
    (packedCenterConsStepCode tromino)
    (packedCenterState periodicStrip packed valid []) 0
    (by simp [packedCenterState, packedNormalizationState])
    (packedCenterState periodicStrip packed valid [])
    (by simp) rfl

@[simp]
theorem packedCenterStepCode_eval_cons
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    (packedCenterStepCode tromino).eval
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      pure (packedCenterState periodicStrip packed
        (valid &&
          (packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool
              tromino periodicStrip cell)) remaining) := by
  exact branchZero_eval_succ_at (get 1) id
    (packedCenterConsStepCode tromino)
    (packedCenterState periodicStrip packed valid
      (cell :: remaining))
    (Encodable.encode (cell :: remaining))
    (by simp [packedCenterState, packedNormalizationState])
    (packedCenterState periodicStrip packed
      (valid &&
        (packed.centerBaseInsideBool tromino periodicStrip cell &&
          packed.centerBaseCoveredBool
            tromino periodicStrip cell)) remaining)
    (packedCenterConsStepCode_eval tromino periodicStrip
      wellFormed packed valid cell remaining)
    (by simp)

/-- Total semantics used by the evaluator-space loop rule. -/
def packedCenterNativeStep
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (values : List Nat) : List Nat :=
  match
      (Encodable.decode (values[1]?.getD 0) :
        Option (List Cell)) with
  | none => values
  | some [] => values
  | some (cell :: remaining) =>
      [Encodable.encode periodicStrip.motif,
        Encodable.encode remaining, periodicStrip.period,
        packed.phase, WindowState.center.val, packed.assignmentWord,
        (decide (values[6]?.getD 0 ≠ 0) &&
          (packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool
              tromino periodicStrip cell)).toNat]

@[simp]
theorem packedCenterNativeStep_state_nil
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool) :
    packedCenterNativeStep tromino periodicStrip packed
        (packedCenterState periodicStrip packed valid []) =
      packedCenterState periodicStrip packed valid [] := by
  simp [packedCenterNativeStep, packedCenterState,
    packedNormalizationState]

@[simp]
theorem packedCenterNativeStep_state_cons
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    packedCenterNativeStep tromino periodicStrip packed
        (packedCenterState periodicStrip packed valid
          (cell :: remaining)) =
      packedCenterState periodicStrip packed
        (valid &&
          (packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool
              tromino periodicStrip cell)) remaining := by
  unfold packedCenterNativeStep
  rw [show
    (Encodable.decode
        ((packedCenterState periodicStrip packed valid
          (cell :: remaining))[1]?.getD 0) : Option (List Cell)) =
      some (cell :: remaining) by
    change Encodable.decode (Encodable.encode (cell :: remaining)) =
      some (cell :: remaining)
    exact Encodable.encodek (cell :: remaining)]
  cases valid <;>
    cases inside :
      packed.centerBaseInsideBool tromino periodicStrip cell <;>
    cases covered :
      packed.centerBaseCoveredBool tromino periodicStrip cell <;>
    simp [packedCenterState, packedNormalizationState,
      inside, covered]

/-- Typed semantics of a fixed number of motif-streaming steps. -/
def packedCenterProcess
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    Nat -> Bool -> List Cell -> List Nat
  | 0, valid, remaining =>
      packedCenterState periodicStrip packed valid remaining
  | steps + 1, valid, [] =>
      packedCenterProcess tromino periodicStrip packed steps valid []
  | steps + 1, valid, cell :: remaining =>
      packedCenterProcess tromino periodicStrip packed steps
        (valid &&
          (packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool
              tromino periodicStrip cell)) remaining

theorem packedCenterNativeStep_iterate
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (steps : Nat) (valid : Bool) (remaining : List Cell) :
    ((packedCenterNativeStep tromino periodicStrip packed)^[steps])
        (packedCenterState periodicStrip packed valid remaining) =
      packedCenterProcess tromino periodicStrip packed
        steps valid remaining := by
  induction steps generalizing valid remaining with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      cases remaining with
      | nil =>
          rw [packedCenterNativeStep_state_nil]
          simpa [packedCenterProcess] using induction valid []
      | cons cell remaining =>
          rw [packedCenterNativeStep_state_cons]
          simpa [packedCenterProcess] using induction
            (valid &&
              (packed.centerBaseInsideBool tromino periodicStrip cell &&
                packed.centerBaseCoveredBool
                  tromino periodicStrip cell)) remaining

theorem packedCenterFlatIterateCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState)
    (steps : Nat) (valid : Bool) (remaining : List Cell) :
    (flatIterate (packedCenterStepCode tromino)).eval
        (steps :: packedCenterState periodicStrip packed valid remaining) =
      pure (packedCenterProcess tromino periodicStrip packed
        steps valid remaining) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing valid remaining with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval, packedCenterProcess]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      cases remaining with
      | nil =>
          refine ⟨steps :: packedCenterState periodicStrip packed
            valid [], ?_, ?_⟩
          · simp [flatCountdownBody, packedCenterStepCode_eval_nil]
          · simpa [packedCenterProcess] using induction valid []
      | cons cell remaining =>
          let nextValid := valid &&
            (packed.centerBaseInsideBool tromino periodicStrip cell &&
              packed.centerBaseCoveredBool
                tromino periodicStrip cell)
          refine ⟨steps :: packedCenterState periodicStrip packed
            nextValid remaining, ?_, ?_⟩
          · simp [flatCountdownBody,
              packedCenterStepCode_eval_cons,
              wellFormed, nextValid]
          · simpa [packedCenterProcess, nextValid] using
              induction nextValid remaining

theorem packedCenterProcess_of_length_le
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (steps : Nat) (valid : Bool) (remaining : List Cell)
    (enough : remaining.length ≤ steps) :
    packedCenterProcess tromino periodicStrip packed
        steps valid remaining =
      packedCenterState periodicStrip packed
        (valid && remaining.all fun cell =>
          packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool
              tromino periodicStrip cell) [] := by
  induction remaining generalizing steps valid with
  | nil =>
      induction steps generalizing valid with
      | zero => simp [packedCenterProcess, packedCenterState]
      | succ steps induction =>
          simpa [packedCenterProcess] using induction valid
  | cons cell remaining induction =>
      cases steps with
      | zero => simp at enough
      | succ steps =>
          have remainingEnough : remaining.length ≤ steps := by
            simpa using enough
          rw [packedCenterProcess]
          rw [induction steps
            (valid &&
              (packed.centerBaseInsideBool tromino periodicStrip cell &&
                packed.centerBaseCoveredBool
                  tromino periodicStrip cell)) remainingEnough]
          simp [packedCenterState, Bool.and_assoc]

private theorem list_all_and
    {α : Type} (items : List α) (left right : α -> Bool) :
    items.all (fun item => left item && right item) =
      (items.all left && items.all right) := by
  induction items with
  | nil => simp
  | cons item items induction =>
      simp [induction, Bool.and_assoc, Bool.and_left_comm]

theorem packedCenterBaseValid_all_eq
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    periodicStrip.motif.all (fun cell =>
        packed.centerBaseInsideBool tromino periodicStrip cell &&
          packed.centerBaseCoveredBool tromino periodicStrip cell) =
      packed.isCenterValidBool tromino periodicStrip := by
  rw [list_all_and]
  rfl

theorem packedCenterProcess_encode
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool) :
    packedCenterProcess tromino periodicStrip packed
        (Encodable.encode periodicStrip.motif)
        valid periodicStrip.motif =
      packedCenterState periodicStrip packed
        (valid && packed.isCenterValidBool tromino periodicStrip) [] := by
  rw [packedCenterProcess_of_length_le tromino periodicStrip packed
    (Encodable.encode periodicStrip.motif) valid periodicStrip.motif
    (length_le_encode periodicStrip.motif)]
  rw [packedCenterBaseValid_all_eq]

/-- Assemble the countdown and initial state from
`[period, phase, motifCode, word]`. -/
def packedCenterLoopInputCode : Code :=
  prepend (get 2) <|
    prepend (get 2) <|
      prepend (get 2) <|
        prepend (get 0) <|
          prepend (get 1) <|
            prepend (numeral WindowState.center.val) <|
              prepend (get 3) one

@[simp]
theorem packedCenterLoopInputCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterLoopInputCode.eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          packed.assignmentWord] =
      pure (Encodable.encode periodicStrip.motif ::
        packedCenterState periodicStrip packed
          true periodicStrip.motif) := by
  simp [packedCenterLoopInputCode, packedCenterState,
    packedNormalizationState]

/-- Scan the complete motif and project packed center validity. -/
def packedCenterValidCode (tromino : Tromino) : Code :=
  (get 6).comp <|
    (flatIterate (packedCenterStepCode tromino)).comp
      packedCenterLoopInputCode

@[simp]
theorem packedCenterValidCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) :
    (packedCenterValidCode tromino).eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          packed.assignmentWord] =
      pure [(packed.isCenterValidBool
        tromino periodicStrip).toNat] := by
  let values := [periodicStrip.period, packed.phase,
    Encodable.encode periodicStrip.motif, packed.assignmentWord]
  have inputRun := packedCenterLoopInputCode_eval periodicStrip packed
  have loopRun := packedCenterFlatIterateCode_eval tromino periodicStrip
    wellFormed packed (Encodable.encode periodicStrip.motif)
    true periodicStrip.motif
  rw [packedCenterProcess_encode] at loopRun
  have composed :
      ((flatIterate (packedCenterStepCode tromino)).comp
          packedCenterLoopInputCode).eval values =
        pure (packedCenterState periodicStrip packed
          (packed.isCenterValidBool tromino periodicStrip) []) := by
    calc
      _ = (flatIterate (packedCenterStepCode tromino)).eval
          (Encodable.encode periodicStrip.motif ::
            packedCenterState periodicStrip packed
              true periodicStrip.motif) := by
        simp [inputRun, values]
      _ = _ := by simpa using loopRun
  calc
    _ = (get 6).eval
        (packedCenterState periodicStrip packed
          (packed.isCenterValidBool tromino periodicStrip) []) := by
      simp [packedCenterValidCode, composed, values]
    _ = _ := by
      simp [packedCenterState, packedNormalizationState]

end Turing.ToPartrec.Code
