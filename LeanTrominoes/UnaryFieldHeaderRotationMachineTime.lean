/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldHeaderRotationMachineExecution

/-! # Polynomial-time certificate for unary strip-header rotation -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryFieldHeaderRotationMachine

open UnaryFieldEncoderMachine

def totalTime (symbols : List Symbol) : Nat :=
  let afterFirst := afterField symbols
  let afterSecond := afterField afterFirst
  let suffix := afterField afterSecond
  fieldScanTime symbols + fieldScanTime afterFirst +
    fieldScanTime afterSecond + (fieldUnits symbols).length + 1 +
      suffix.length + 1 +
        (UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo symbols).length + 1

theorem initList_eq_scanFirstCfg (symbols : List Symbol) :
    initList machine symbols = scanFirstCfg ⟨symbols, [], [], []⟩ := by
  unfold initList machine scanFirstCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List Symbol) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem haltDataCfg_empty_eq_haltCfg (output : List Symbol) :
    haltDataCfg ⟨[], [], [], output⟩ = haltCfg output :=
  rfl

/-- Complete exact execution of the fixed header permutation machine. -/
def machine_outputsInTime (symbols : List Symbol) :
    TM2OutputsInTime machine symbols
      (some (UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo symbols))
      (totalTime symbols) := by
  let afterFirst := afterField symbols
  let afterSecond := afterField afterFirst
  let suffix := afterField afterSecond
  let first := fieldUnits symbols
  let second := normalizedField afterFirst
  let third := normalizedField afterSecond
  let firstField := normalizedField symbols
  let rotated :=
    UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo symbols
  let initial : TapeData := ⟨symbols, [], [], []⟩
  let firstScanned : TapeData := ⟨afterFirst, first.reverse, [], []⟩
  let secondScanned : TapeData :=
    ⟨afterSecond, first.reverse, second.reverse, []⟩
  let thirdScanned : TapeData :=
    ⟨suffix, first.reverse, third.reverse ++ second.reverse, []⟩
  let firstEmitted : TapeData :=
    ⟨suffix, [], (second ++ third ++ firstField).reverse, []⟩
  let suffixCopied : TapeData :=
    ⟨[], [], rotated.reverse, []⟩
  have firstRun := scanFirst_evalsInTime symbols initial rfl
  have secondRun := scanSecond_evalsInTime afterFirst firstScanned rfl
  have firstTwo := EvalsToInTime.trans (TM2.step program)
    (fieldScanTime symbols) (fieldScanTime afterFirst)
    (scanFirstCfg initial) (scanSecondCfg firstScanned)
    (some (scanThirdCfg secondScanned))
    (by simpa [initial, firstScanned, afterFirst, first] using firstRun)
    (by simpa [firstScanned, secondScanned, afterSecond, second] using
      secondRun)
  have thirdRun := scanThird_evalsInTime afterSecond secondScanned rfl
  have firstThree := EvalsToInTime.trans (TM2.step program)
    (fieldScanTime afterFirst + fieldScanTime symbols)
    (fieldScanTime afterSecond)
    (scanFirstCfg initial) (scanThirdCfg secondScanned)
    (some (emitFirstCfg thirdScanned)) firstTwo
    (by simpa [secondScanned, thirdScanned, suffix, third] using thirdRun)
  have firstEmitRun := emitFirst_evalsInTime first.reverse thirdScanned rfl
  have throughFirst := EvalsToInTime.trans (TM2.step program)
    (fieldScanTime afterSecond +
      (fieldScanTime afterFirst + fieldScanTime symbols))
    (first.reverse.length + 1)
    (scanFirstCfg initial) (emitFirstCfg thirdScanned)
    (some (copySuffixCfg firstEmitted)) firstThree
    (by
      simpa [thirdScanned, firstEmitted, firstField, first, normalizedField,
        List.reverse_append, List.append_assoc] using firstEmitRun)
  have suffixRun := copySuffix_evalsInTime suffix firstEmitted rfl
  have throughSuffix := EvalsToInTime.trans (TM2.step program)
    (first.reverse.length + 1 +
      (fieldScanTime afterSecond +
        (fieldScanTime afterFirst + fieldScanTime symbols)))
    (suffix.length + 1)
    (scanFirstCfg initial) (copySuffixCfg firstEmitted)
    (some (reverseOutputCfg suffixCopied)) throughFirst
    (by
      simpa [suffixCopied, firstEmitted, rotated, afterFirst, afterSecond,
        suffix, second, third, firstField,
        rotateFirstFieldAfterTwo_eq_normalizedFields,
        List.reverse_append, List.append_assoc] using suffixRun)
  have reverseRun := reverseOutput_evalsInTime
    rotated.reverse suffixCopied rfl
  have whole := EvalsToInTime.trans (TM2.step program)
    (suffix.length + 1 +
      (first.reverse.length + 1 +
        (fieldScanTime afterSecond +
          (fieldScanTime afterFirst + fieldScanTime symbols))))
    (rotated.reverse.length + 1)
    (scanFirstCfg initial) (reverseOutputCfg suffixCopied)
    (some (haltDataCfg ⟨[], [], [], rotated⟩)) throughSuffix
    (by simpa [suffixCopied, rotated] using reverseRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step program))^[whole.steps]
        (some (initList machine symbols)) =
          some (haltList machine rotated)
    rw [initList_eq_scanFirstCfg, haltList_eq_haltCfg,
      ← haltDataCfg_empty_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · apply whole.steps_le_m.trans
    simp only [totalTime, afterFirst, afterSecond, suffix, first, rotated,
      List.length_reverse]
    omega

theorem fieldUnits_length_le (symbols : List Symbol) :
    (fieldUnits symbols).length ≤ symbols.length := by
  induction symbols with
  | nil => simp [fieldUnits]
  | cons symbol symbols induction =>
      cases symbol <;> simp [fieldUnits] at *
      all_goals omega

theorem afterField_length_le (symbols : List Symbol) :
    (afterField symbols).length ≤ symbols.length := by
  induction symbols with
  | nil => simp [afterField]
  | cons symbol symbols induction =>
      cases symbol <;> simp [afterField] at *
      all_goals omega

theorem fieldScanTime_le (symbols : List Symbol) :
    fieldScanTime symbols ≤ symbols.length + 1 := by
  induction symbols with
  | nil => simp [fieldScanTime]
  | cons symbol symbols induction =>
      cases symbol <;> simp [fieldScanTime] at *
      all_goals omega

theorem normalizedField_length_le (symbols : List Symbol) :
    (normalizedField symbols).length ≤ symbols.length + 1 := by
  simp [normalizedField]
  exact fieldUnits_length_le symbols

theorem rotateFirstFieldAfterTwo_length_le (symbols : List Symbol) :
    (UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo symbols).length ≤
      4 * symbols.length + 3 := by
  rw [rotateFirstFieldAfterTwo_eq_normalizedFields]
  simp only [List.length_append]
  have first := normalizedField_length_le symbols
  have second := normalizedField_length_le (afterField symbols)
  have third := normalizedField_length_le (afterField (afterField symbols))
  have afterFirstLe := afterField_length_le symbols
  have afterSecondLe :=
    (afterField_length_le (afterField symbols)).trans afterFirstLe
  have suffixLe :=
    (afterField_length_le (afterField (afterField symbols))).trans
      afterSecondLe
  omega

theorem totalTime_le (symbols : List Symbol) :
    totalTime symbols ≤ 9 * symbols.length + 9 := by
  have firstScan := fieldScanTime_le symbols
  have secondScan := fieldScanTime_le (afterField symbols)
  have thirdScan := fieldScanTime_le (afterField (afterField symbols))
  have firstUnits := fieldUnits_length_le symbols
  have afterFirstLe := afterField_length_le symbols
  have afterSecondLe :=
    (afterField_length_le (afterField symbols)).trans afterFirstLe
  have suffixLe :=
    (afterField_length_le (afterField (afterField symbols))).trans
      afterSecondLe
  have output := rotateFirstFieldAfterTwo_length_le symbols
  simp only [totalTime]
  omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 9 * Polynomial.X + Polynomial.C 9

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 9 * length + 9 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Moving a unary count behind two header fields is polynomial-time (indeed
linear-time) on arbitrary symbol streams. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Symbol) (List Symbol) Symbol Symbol id id
      UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun symbols := by
    have run := machine_outputsInTime symbols
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Symbol).invFun (id symbols))
        (some (List.map (Equiv.refl Symbol).invFun
          (id (UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo symbols))))
        (totalTime symbols) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le symbols) }

end UnaryFieldHeaderRotationMachine
end LeanTrominoes
