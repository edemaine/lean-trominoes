/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedNormalizationAt

/-!
# Complete packed normalization of one column over a flat motif

The indexed one-cell predicate is lifted through exactly the explicit motif
length.  Coordinates remain fixed; only the validity accumulator and motif
index change.
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

/-- Flat transition context before a motif-wide pass. -/
def flatPackedTransitionContext
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : List Nat :=
  [periodicStrip.width, periodicStrip.period,
    periodicStrip.motif.length, current.assignmentWord, current.phase,
    next.assignmentWord, next.phase] ++
      periodicStrip.motif.flatMap
        PeriodicStripFlatEncoding.cellFields

def flatPackedNormalizationUpdatedValidCode
    (column : WindowColumn) : Code :=
  boolAnd (get 0) (flatPackedNormalizedAtCode column)

@[simp]
theorem flatPackedNormalizationUpdatedValidCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedNormalizationUpdatedValidCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        [(valid &&
          current.normalizedAtBool periodicStrip column cell).toNat] := by
  have headRun := flatPackedNormalizedAtCode_eval
    column periodicStrip current next valid processed cell remaining split
  have combined := boolAnd_eval_at (get 0)
    (flatPackedNormalizedAtCode column)
    (flatPackedTransitionScanState periodicStrip current next
      valid processed.length)
    valid.toNat
    (current.normalizedAtBool periodicStrip column cell).toNat
    (by simp [flatPackedTransitionScanState]) headRun
  cases valid <;>
    cases normalized :
      current.normalizedAtBool periodicStrip column cell <;>
    simpa [flatPackedNormalizationUpdatedValidCode,
      normalized] using combined

/-- Consume one indexed motif position while retaining the full flat motif. -/
def flatPackedNormalizationStepCode
    (column : WindowColumn) : Code :=
  prepend (flatPackedNormalizationUpdatedValidCode column) <|
    prepend (succ.comp (get 1)) (drop 2)

@[simp]
theorem flatPackedNormalizationStepCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedNormalizationStepCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (valid && current.normalizedAtBool periodicStrip column cell)
          (processed.length + 1)) := by
  have updatedRun := flatPackedNormalizationUpdatedValidCode_eval
    column periodicStrip current next valid processed cell remaining split
  simp only [flatPackedNormalizationStepCode, prepend_eval_eq]
  rw [updatedRun]
  simp [flatPackedTransitionScanState]

/-- Scanning a semantic suffix accumulates normalization and advances the
index to the end of the fixed motif. -/
theorem flatPackedNormalizationIterateCode_eval_from
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    (flatIterate (flatPackedNormalizationStepCode column)).eval
        (remaining.length ::
          flatPackedTransitionScanState periodicStrip current next
            valid processed.length) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (valid && remaining.all fun cell =>
            current.normalizedAtBool periodicStrip column cell)
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
      let nextValid :=
        valid && current.normalizedAtBool periodicStrip column cell
      have headSplit :
          periodicStrip.motif = processed ++ cell :: remaining := by
        simpa [List.append_assoc] using split
      have nextSplit :
          periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have stepRun := flatPackedNormalizationStepCode_eval
        column periodicStrip current next valid processed cell remaining
          headSplit
      refine
        ⟨remaining.length ::
            flatPackedTransitionScanState periodicStrip current next
              nextValid nextProcessed.length,
          ?_, ?_⟩
      · simp [flatCountdownBody, stepRun,
          nextProcessed, nextValid]
      · simpa [nextProcessed, nextValid, Bool.and_assoc] using
          induction nextValid nextProcessed nextSplit

theorem flatPackedNormalizationIterateCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (flatIterate (flatPackedNormalizationStepCode column)).eval
        (periodicStrip.motif.length ::
          flatPackedTransitionScanState periodicStrip current next true 0) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (current.normalizedColumnBool periodicStrip column)
          periodicStrip.motif.length) := by
  have run := flatPackedNormalizationIterateCode_eval_from
    column periodicStrip current next true [] periodicStrip.motif (by simp)
  simpa [PackedWindowState.normalizedColumnBool] using run

/-- Insert countdown, validity, and zero index before the seven-field flat
transition context. -/
def flatPackedNormalizationLoopInputCode : Code :=
  prepend (get 2) <|
    prepend one <|
      prepend zero id

@[simp]
theorem flatPackedNormalizationLoopInputCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationLoopInputCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure
        (periodicStrip.motif.length ::
          flatPackedTransitionScanState periodicStrip current next true 0) := by
  simp [flatPackedNormalizationLoopInputCode,
    flatPackedTransitionContext, flatPackedTransitionScanState]

/-- Complete flat normalization check for one frontier column. -/
def flatPackedNormalizationColumnCode
    (column : WindowColumn) : Code :=
  (get 0).comp <|
    (flatIterate (flatPackedNormalizationStepCode column)).comp
      flatPackedNormalizationLoopInputCode

@[simp]
theorem flatPackedNormalizationColumnCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (flatPackedNormalizationColumnCode column).eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure
        [(current.normalizedColumnBool periodicStrip column).toNat] := by
  have inputRun := flatPackedNormalizationLoopInputCode_eval
    periodicStrip current next
  have loopRun := flatPackedNormalizationIterateCode_eval
    column periodicStrip current next
  have composed :
      ((flatIterate (flatPackedNormalizationStepCode column)).comp
        flatPackedNormalizationLoopInputCode).eval
          (flatPackedTransitionContext periodicStrip current next) =
        pure
          (flatPackedTransitionScanState periodicStrip current next
            (current.normalizedColumnBool periodicStrip column)
            periodicStrip.motif.length) := by
    calc
      _ = (flatIterate
          (flatPackedNormalizationStepCode column)).eval
            (periodicStrip.motif.length ::
              flatPackedTransitionScanState periodicStrip current next
                true 0) := comp_eval_pure _ _ _ _ inputRun
      _ = _ := loopRun
  calc
    _ = (get 0).eval
        (flatPackedTransitionScanState periodicStrip current next
          (current.normalizedColumnBool periodicStrip column)
          periodicStrip.motif.length) :=
      comp_eval_pure _ _ _ _ composed
    _ = _ := by simp [flatPackedTransitionScanState]

end Turing.ToPartrec.Code
