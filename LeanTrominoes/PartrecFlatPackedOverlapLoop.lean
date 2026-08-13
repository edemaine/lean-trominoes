import LeanTrominoes.PartrecFlatPackedNormalizationLoop
import LeanTrominoes.PartrecFlatPackedOverlapAt

/-!
# Streaming flat packed overlap over the motif

One indexed assignment comparison is lifted through the explicit motif length
for each of the four columns shared by adjacent packed windows.  Every pass
retains the full flat coordinate stream in the common transition context.
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

/-- Assemble one fixed shared-column comparison from the indexed transition
scan state. -/
def flatPackedOverlapAtArgumentsCode (column : Fin 4) : Code :=
  prepend (get 4) <|
    prepend (numeral column.succ.val) <|
      prepend (numeral column.castSucc.val) <|
        prepend (flatPackedTransitionCellFieldCode (0 : Fin 2)) <|
          prepend (flatPackedTransitionCellFieldCode (1 : Fin 2)) <|
            prepend (get 5) <|
              prepend (get 7) (drop 9)

@[simp]
theorem flatPackedOverlapAtArgumentsCode_eval
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedOverlapAtArgumentsCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure (flatPackedOverlapAtInput periodicStrip.motif
        column.succ.val column.castSucc.val cell
        current.assignmentWord next.assignmentWord) := by
  have xRun := flatPackedTransitionCellFieldCode_eval
    (0 : Fin 2) periodicStrip current next valid processed cell remaining split
  have yRun := flatPackedTransitionCellFieldCode_eval
    (1 : Fin 2) periodicStrip current next valid processed cell remaining split
  let scanState := flatPackedTransitionScanState periodicStrip
    current next valid processed.length
  simp only [flatPackedOverlapAtArgumentsCode, prepend_eval_eq]
  rw [show (get 4).eval scanState =
      pure [periodicStrip.motif.length] by
    simp [scanState, flatPackedTransitionScanState]]
  rw [show (numeral column.succ.val).eval scanState =
      pure [column.succ.val] by simp]
  rw [show (numeral column.castSucc.val).eval scanState =
      pure [column.castSucc.val] by simp]
  rw [xRun, yRun]
  rw [show (get 5).eval scanState = pure [current.assignmentWord] by
    simp [scanState, flatPackedTransitionScanState]]
  rw [show (get 7).eval scanState = pure [next.assignmentWord] by
    simp [scanState, flatPackedTransitionScanState]]
  simp [flatPackedTransitionScanState, flatPackedOverlapAtInput,
    PeriodicStripFlatEncoding.cellFields]

/-- Compare current and next assignments at the indexed motif cell for one
shared column. -/
def flatPackedOverlapAtIndexedCode (column : Fin 4) : Code :=
  flatPackedOverlapAtCode.comp
    (flatPackedOverlapAtArgumentsCode column)

@[simp]
theorem flatPackedOverlapAtIndexedCode_eval
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedOverlapAtIndexedCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure [(current.overlapsAtBool periodicStrip
        next column cell).toNat] := by
  have arguments := flatPackedOverlapAtArgumentsCode_eval
    column periodicStrip current next valid processed cell remaining split
  have overlap := flatPackedOverlapAtCode_eval_semantic
    periodicStrip current next column cell
  simpa only [flatPackedOverlapAtIndexedCode] using
    (comp_eval_pure _ _ _ _ arguments).trans overlap

/-- Conjoin the indexed overlap comparison with the loop accumulator. -/
def flatPackedOverlapUpdatedValidCode (column : Fin 4) : Code :=
  boolAnd (get 0) (flatPackedOverlapAtIndexedCode column)

@[simp]
theorem flatPackedOverlapUpdatedValidCode_eval
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedOverlapUpdatedValidCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure [(valid && current.overlapsAtBool
        periodicStrip next column cell).toNat] := by
  have overlapRun := flatPackedOverlapAtIndexedCode_eval
    column periodicStrip current next valid processed cell remaining split
  have combined := boolAnd_eval_at (get 0)
    (flatPackedOverlapAtIndexedCode column)
    (flatPackedTransitionScanState periodicStrip current next
      valid processed.length)
    valid.toNat
    (current.overlapsAtBool periodicStrip next column cell).toNat
    (by simp [flatPackedTransitionScanState]) overlapRun
  cases valid <;>
    cases overlap :
      current.overlapsAtBool periodicStrip next column cell <;>
    simpa [flatPackedOverlapUpdatedValidCode, overlap] using combined

/-- Consume one indexed motif position for one overlap column. -/
def flatPackedOverlapStepCode (column : Fin 4) : Code :=
  prepend (flatPackedOverlapUpdatedValidCode column) <|
    prepend (succ.comp (get 1)) (drop 2)

@[simp]
theorem flatPackedOverlapStepCode_eval
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedOverlapStepCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (valid && current.overlapsAtBool
            periodicStrip next column cell)
          (processed.length + 1)) := by
  have updatedRun := flatPackedOverlapUpdatedValidCode_eval
    column periodicStrip current next valid processed cell remaining split
  simp only [flatPackedOverlapStepCode, prepend_eval_eq]
  rw [updatedRun]
  simp [flatPackedTransitionScanState]

theorem flatPackedOverlapIterateCode_eval_from
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    (flatIterate (flatPackedOverlapStepCode column)).eval
        (remaining.length ::
          flatPackedTransitionScanState periodicStrip current next
            valid processed.length) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (valid && remaining.all fun cell =>
            current.overlapsAtBool periodicStrip next column cell)
          periodicStrip.motif.length) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction remaining generalizing processed valid with
  | nil =>
      have motifEq : periodicStrip.motif = processed := by
        simpa using split
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval, motifEq,
        flatPackedTransitionScanState]
  | cons cell remaining induction =>
      apply PFun.mem_fix_iff.mpr
      right
      let nextProcessed := processed ++ [cell]
      let nextValid := valid &&
        current.overlapsAtBool periodicStrip next column cell
      have headSplit :
          periodicStrip.motif = processed ++ cell :: remaining := by
        simpa [List.append_assoc] using split
      have nextSplit :
          periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have stepRun := flatPackedOverlapStepCode_eval
        column periodicStrip current next valid
          processed cell remaining headSplit
      refine
        ⟨remaining.length ::
            flatPackedTransitionScanState periodicStrip current next
              nextValid nextProcessed.length,
          ?_, ?_⟩
      · simp [flatCountdownBody, stepRun,
          nextProcessed, nextValid]
      · simpa [nextProcessed, nextValid, Bool.and_assoc] using
          induction nextValid nextProcessed nextSplit

theorem flatPackedOverlapIterateCode_eval
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (flatIterate (flatPackedOverlapStepCode column)).eval
        (periodicStrip.motif.length ::
          flatPackedTransitionScanState periodicStrip current next true 0) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (current.overlapsColumnBool periodicStrip next column)
          periodicStrip.motif.length) := by
  have run := flatPackedOverlapIterateCode_eval_from
    column periodicStrip current next true [] periodicStrip.motif (by simp)
  simpa [PackedWindowState.overlapsColumnBool] using run

/-- One overlap-column scan uses the common transition-loop preparation. -/
def flatPackedOverlapLoopInputCode : Code :=
  flatPackedNormalizationLoopInputCode

@[simp]
theorem flatPackedOverlapLoopInputCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapLoopInputCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure
        (periodicStrip.motif.length ::
          flatPackedTransitionScanState periodicStrip current next true 0) := by
  exact flatPackedNormalizationLoopInputCode_eval
    periodicStrip current next

/-- Scan one complete flat motif column and project its overlap tag. -/
def flatPackedOverlapColumnCode (column : Fin 4) : Code :=
  (get 0).comp <|
    (flatIterate (flatPackedOverlapStepCode column)).comp
      flatPackedOverlapLoopInputCode

@[simp]
theorem flatPackedOverlapColumnCode_eval
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (flatPackedOverlapColumnCode column).eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure
        [(current.overlapsColumnBool periodicStrip
          next column).toNat] := by
  have inputRun := flatPackedOverlapLoopInputCode_eval
    periodicStrip current next
  have loopRun := flatPackedOverlapIterateCode_eval
    column periodicStrip current next
  have composed :
      ((flatIterate (flatPackedOverlapStepCode column)).comp
        flatPackedOverlapLoopInputCode).eval
          (flatPackedTransitionContext periodicStrip current next) =
        pure
          (flatPackedTransitionScanState periodicStrip current next
            (current.overlapsColumnBool periodicStrip next column)
            periodicStrip.motif.length) := by
    calc
      _ = (flatIterate (flatPackedOverlapStepCode column)).eval
          (periodicStrip.motif.length ::
            flatPackedTransitionScanState periodicStrip current next
              true 0) := comp_eval_pure _ _ _ _ inputRun
      _ = _ := loopRun
  calc
    _ = (get 0).eval
        (flatPackedTransitionScanState periodicStrip current next
          (current.overlapsColumnBool periodicStrip next column)
          periodicStrip.motif.length) :=
      comp_eval_pure _ _ _ _ composed
    _ = _ := by simp [flatPackedTransitionScanState]

private theorem boolAnd_bool_eval_at
    (left right : Code) (values : List Nat)
    (leftValue rightValue : Bool)
    (leftCorrect : left.eval values = pure [leftValue.toNat])
    (rightCorrect : right.eval values = pure [rightValue.toNat]) :
    (boolAnd left right).eval values =
      pure [(leftValue && rightValue).toNat] := by
  have combined := boolAnd_eval_at left right values
    leftValue.toNat rightValue.toNat leftCorrect rightCorrect
  cases leftValue <;> cases rightValue <;> simpa using combined

/-- Conjoin the four flat shared-column scans. -/
def flatPackedOverlapColumnsCode : Code :=
  boolAnd (flatPackedOverlapColumnCode (0 : Fin 4)) <|
    boolAnd (flatPackedOverlapColumnCode (1 : Fin 4)) <|
      boolAnd (flatPackedOverlapColumnCode (2 : Fin 4))
        (flatPackedOverlapColumnCode (3 : Fin 4))

@[simp]
theorem flatPackedOverlapColumnsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapColumnsCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure
        [((List.finRange 4).all fun column =>
          current.overlapsColumnBool periodicStrip next column).toNat] := by
  let values := flatPackedTransitionContext periodicStrip current next
  have third :=
    boolAnd_bool_eval_at
      (flatPackedOverlapColumnCode (2 : Fin 4))
      (flatPackedOverlapColumnCode (3 : Fin 4))
      values
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4))
      (current.overlapsColumnBool periodicStrip next (3 : Fin 4))
      (flatPackedOverlapColumnCode_eval 2 periodicStrip current next)
      (flatPackedOverlapColumnCode_eval 3 periodicStrip current next)
  have second :=
    boolAnd_bool_eval_at
      (flatPackedOverlapColumnCode (1 : Fin 4))
      (boolAnd (flatPackedOverlapColumnCode (2 : Fin 4))
        (flatPackedOverlapColumnCode (3 : Fin 4)))
      values
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4))
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool periodicStrip next (3 : Fin 4))
      (flatPackedOverlapColumnCode_eval 1 periodicStrip current next)
      third
  have first :=
    boolAnd_bool_eval_at
      (flatPackedOverlapColumnCode (0 : Fin 4))
      (boolAnd (flatPackedOverlapColumnCode (1 : Fin 4)) <|
        boolAnd (flatPackedOverlapColumnCode (2 : Fin 4))
          (flatPackedOverlapColumnCode (3 : Fin 4)))
      values
      (current.overlapsColumnBool periodicStrip next (0 : Fin 4))
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
        (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
          current.overlapsColumnBool periodicStrip next (3 : Fin 4)))
      (flatPackedOverlapColumnCode_eval 0 periodicStrip current next)
      second
  simpa [flatPackedOverlapColumnsCode, values,
    List.finRange_succ] using first

end Turing.ToPartrec.Code
