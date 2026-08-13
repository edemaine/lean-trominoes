import LeanTrominoes.PartrecFlatPackedCenterBase
import LeanTrominoes.PartrecFlatPackedNormalizationLoop
import LeanTrominoes.PartrecPackedCenterLoop

/-!
# Streaming flat packed center validity over the motif

The one-base center checker is lifted through exactly the explicit motif
length.  The shared indexed transition-scan state retains the full flat
coordinate stream; only the validity accumulator and motif index change.
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

/-- Assemble the one-base flat center input from the shared indexed scan
state. -/
def flatPackedCenterBaseArgumentsCode : Code :=
  prepend (get 3) <|
    prepend (get 6) <|
      prepend (get 4) <|
        prepend (flatPackedTransitionCellFieldCode (0 : Fin 2)) <|
          prepend (flatPackedTransitionCellFieldCode (1 : Fin 2)) <|
            prepend (get 5) (drop 9)

@[simp]
theorem flatPackedCenterBaseArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterBaseArgumentsCode.eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure (flatPackedCenterCandidateInput
        periodicStrip current cell) := by
  have xRun := flatPackedTransitionCellFieldCode_eval
    (0 : Fin 2) periodicStrip current next valid processed cell remaining split
  have yRun := flatPackedTransitionCellFieldCode_eval
    (1 : Fin 2) periodicStrip current next valid processed cell remaining split
  let scanState := flatPackedTransitionScanState periodicStrip
    current next valid processed.length
  simp only [flatPackedCenterBaseArgumentsCode, prepend_eval_eq]
  rw [show (get 3).eval scanState = pure [periodicStrip.period] by
    simp [scanState, flatPackedTransitionScanState]]
  rw [show (get 6).eval scanState = pure [current.phase] by
    simp [scanState, flatPackedTransitionScanState]]
  rw [show (get 4).eval scanState =
      pure [periodicStrip.motif.length] by
    simp [scanState, flatPackedTransitionScanState]]
  rw [xRun, yRun]
  rw [show (get 5).eval scanState = pure [current.assignmentWord] by
    simp [scanState, flatPackedTransitionScanState]]
  simp [flatPackedTransitionScanState,
    flatPackedCenterCandidateInput,
    PeriodicStripFlatEncoding.cellFields]

/-- Check both center conditions at the indexed motif cell. -/
def flatPackedCenterBaseAtCode (tromino : Tromino) : Code :=
  (flatPackedCenterBaseValidCode tromino).comp
    flatPackedCenterBaseArgumentsCode

@[simp]
theorem flatPackedCenterBaseAtCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedCenterBaseAtCode tromino).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure [((current.centerBaseInsideBool
          tromino periodicStrip cell) &&
        current.centerBaseCoveredBool
          tromino periodicStrip cell).toNat] := by
  have arguments := flatPackedCenterBaseArgumentsCode_eval
    periodicStrip current next valid processed cell remaining split
  have baseRun := flatPackedCenterBaseValidCode_eval_semantic
    tromino periodicStrip wellFormed current cell
  simpa only [flatPackedCenterBaseAtCode] using
    (comp_eval_pure _ _ _ _ arguments).trans baseRun

/-- Conjoin the indexed cell's center validity with the loop accumulator. -/
def flatPackedCenterUpdatedValidCode (tromino : Tromino) : Code :=
  boolAnd (get 0) (flatPackedCenterBaseAtCode tromino)

@[simp]
theorem flatPackedCenterUpdatedValidCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedCenterUpdatedValidCode tromino).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure [(valid &&
        (current.centerBaseInsideBool tromino periodicStrip cell &&
          current.centerBaseCoveredBool
            tromino periodicStrip cell)).toNat] := by
  have headRun := flatPackedCenterBaseAtCode_eval
    tromino periodicStrip wellFormed current next valid
      processed cell remaining split
  have combined := boolAnd_eval_at (get 0)
    (flatPackedCenterBaseAtCode tromino)
    (flatPackedTransitionScanState periodicStrip current next
      valid processed.length)
    valid.toNat
    ((current.centerBaseInsideBool tromino periodicStrip cell &&
      current.centerBaseCoveredBool
        tromino periodicStrip cell).toNat)
    (by simp [flatPackedTransitionScanState]) headRun
  cases valid <;>
    cases inside :
      current.centerBaseInsideBool tromino periodicStrip cell <;>
    cases covered :
      current.centerBaseCoveredBool tromino periodicStrip cell <;>
    simpa [flatPackedCenterUpdatedValidCode,
      inside, covered] using combined

/-- Consume one indexed motif position while retaining the flat motif. -/
def flatPackedCenterStepCode (tromino : Tromino) : Code :=
  prepend (flatPackedCenterUpdatedValidCode tromino) <|
    prepend (succ.comp (get 1)) (drop 2)

@[simp]
theorem flatPackedCenterStepCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedCenterStepCode tromino).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (valid &&
            (current.centerBaseInsideBool tromino periodicStrip cell &&
              current.centerBaseCoveredBool
                tromino periodicStrip cell))
          (processed.length + 1)) := by
  have updatedRun := flatPackedCenterUpdatedValidCode_eval
    tromino periodicStrip wellFormed current next valid
      processed cell remaining split
  simp only [flatPackedCenterStepCode, prepend_eval_eq]
  rw [updatedRun]
  simp [flatPackedTransitionScanState]

/-- Scanning a semantic suffix accumulates center validity and advances to the
end of the fixed motif. -/
theorem flatPackedCenterIterateCode_eval_from
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    (flatIterate (flatPackedCenterStepCode tromino)).eval
        (remaining.length ::
          flatPackedTransitionScanState periodicStrip current next
            valid processed.length) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (valid && remaining.all fun cell =>
            current.centerBaseInsideBool tromino periodicStrip cell &&
              current.centerBaseCoveredBool
                tromino periodicStrip cell)
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
        (current.centerBaseInsideBool tromino periodicStrip cell &&
          current.centerBaseCoveredBool
            tromino periodicStrip cell)
      have headSplit :
          periodicStrip.motif = processed ++ cell :: remaining := by
        simpa [List.append_assoc] using split
      have nextSplit :
          periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have stepRun := flatPackedCenterStepCode_eval
        tromino periodicStrip wellFormed current next valid
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

theorem flatPackedCenterIterateCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (flatIterate (flatPackedCenterStepCode tromino)).eval
        (periodicStrip.motif.length ::
          flatPackedTransitionScanState periodicStrip current next true 0) =
      pure
        (flatPackedTransitionScanState periodicStrip current next
          (current.isCenterValidBool tromino periodicStrip)
          periodicStrip.motif.length) := by
  have run := flatPackedCenterIterateCode_eval_from
    tromino periodicStrip wellFormed current next true []
      periodicStrip.motif (by simp)
  rw [packedCenterBaseValid_all_eq] at run
  simpa using run

/-- The center scan has the same countdown/accumulator/index preparation as
the flat normalization scan. -/
def flatPackedCenterLoopInputCode : Code :=
  flatPackedNormalizationLoopInputCode

@[simp]
theorem flatPackedCenterLoopInputCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedCenterLoopInputCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure
        (periodicStrip.motif.length ::
          flatPackedTransitionScanState periodicStrip current next true 0) := by
  exact flatPackedNormalizationLoopInputCode_eval
    periodicStrip current next

/-- Scan the complete flat motif and project packed center validity. -/
def flatPackedCenterValidCode (tromino : Tromino) : Code :=
  (get 0).comp <|
    (flatIterate (flatPackedCenterStepCode tromino)).comp
      flatPackedCenterLoopInputCode

@[simp]
theorem flatPackedCenterValidCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (flatPackedCenterValidCode tromino).eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [(current.isCenterValidBool
        tromino periodicStrip).toNat] := by
  have inputRun := flatPackedCenterLoopInputCode_eval
    periodicStrip current next
  have loopRun := flatPackedCenterIterateCode_eval
    tromino periodicStrip wellFormed current next
  have composed :
      ((flatIterate (flatPackedCenterStepCode tromino)).comp
        flatPackedCenterLoopInputCode).eval
          (flatPackedTransitionContext periodicStrip current next) =
        pure
          (flatPackedTransitionScanState periodicStrip current next
            (current.isCenterValidBool tromino periodicStrip)
            periodicStrip.motif.length) := by
    calc
      _ = (flatIterate (flatPackedCenterStepCode tromino)).eval
          (periodicStrip.motif.length ::
            flatPackedTransitionScanState periodicStrip current next
              true 0) := comp_eval_pure _ _ _ _ inputRun
      _ = _ := loopRun
  calc
    _ = (get 0).eval
        (flatPackedTransitionScanState periodicStrip current next
          (current.isCenterValidBool tromino periodicStrip)
          periodicStrip.motif.length) :=
      comp_eval_pure _ _ _ _ composed
    _ = _ := by simp [flatPackedTransitionScanState]

end Turing.ToPartrec.Code
