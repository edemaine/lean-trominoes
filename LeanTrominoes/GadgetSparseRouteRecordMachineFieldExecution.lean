/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineRouteExecution

/-! # Unary metadata-field executions for route records -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

def zeroSteps {Configuration : Type}
    {transition : Configuration → Option Configuration}
    (configuration : Configuration) :
    EvalsToInTime transition configuration (some configuration) 0 where
  steps := 0
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl 0

/-- Consume a unary period field and accumulate its units on the complement
counter. -/
def scanPeriodUnits_evalsInTime (word : List Unit)
    (rest : List InputToken) (data : TapeData)
    (inputEq : data.input =
      List.replicate word.length .unit ++ .periodEnd :: rest) :
    EvalsToInTime (TM2.step program)
      (scanPeriodCfg data)
      (some (scanHorizontalCfg
        { data with
          input := rest
          horizontalComplement := word.reverse ++
            data.horizontalComplement }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_scanPeriod_periodEnd data rest (by
        simpa using inputEq))
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let remainingInput :=
        List.replicate word.length
          GadgetSparseRouteRasterNormalizedTokens.Token.unit ++
            .periodEnd :: rest
      let nextData : TapeData :=
        { data with
          input := remainingInput
          horizontalComplement := () :: data.horizontalComplement }
      have first := oneStep (step_scanPeriod_unit data remainingInput (by
        simpa [remainingInput, List.replicate_succ] using inputEq))
      have remaining := induction nextData (by simp [nextData, remainingInput])
      have whole := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (scanPeriodCfg data) (scanPeriodCfg nextData)
        (some (scanHorizontalCfg
          { nextData with
            input := rest
            horizontalComplement := word.reverse ++
              nextData.horizontalComplement })) first remaining
      convert whole using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Move a unary horizontal field from the complement counter to the live
horizontal counter.  `word` is physically present at the head of the
complement, so underflow is impossible in this execution. -/
def scanHorizontalUnits_evalsInTime (word complementRest : List Unit)
    (rest : List InputToken) (data : TapeData)
    (inputEq : data.input =
      List.replicate word.length .unit ++ rest)
    (complementEq : data.horizontalComplement = word ++ complementRest) :
    EvalsToInTime (TM2.step program)
      (scanHorizontalCfg data)
      (some (scanHorizontalCfg
        { data with
          input := rest
          horizontal := word.reverse ++ data.horizontal
          horizontalComplement := complementRest }))
      (2 * word.length) := by
  induction word generalizing data with
  | nil =>
      have same : scanHorizontalCfg data = scanHorizontalCfg
          { data with
            input := rest
            horizontal := [].reverse ++ data.horizontal
            horizontalComplement := complementRest } := by
        simp only [List.length_nil, List.replicate_zero,
          List.nil_append] at inputEq complementEq
        rcases data with ⟨input, horizontal, complement, positive,
          negative, scratch, outputReverse, output⟩
        change input = rest at inputEq
        change complement = complementRest at complementEq
        subst input
        subst complement
        rfl
      simpa [same] using zeroSteps (scanHorizontalCfg data)
  | cons head word induction =>
      rcases head with ⟨⟩
      let remainingInput := List.replicate word.length
        GadgetSparseRouteRasterNormalizedTokens.Token.unit ++ rest
      let afterScan : TapeData := { data with input := remainingInput }
      let nextData : TapeData :=
        { afterScan with
          horizontal := () :: data.horizontal
          horizontalComplement := word ++ complementRest }
      have scanned := oneStep (step_scanHorizontal_unit data remainingInput (by
        simpa [remainingInput, List.replicate_succ] using inputEq))
      have moved := oneStep (step_moveHorizontal_cons
        afterScan (word ++ complementRest) (by
          simp [afterScan, complementEq]))
      have firstTwo := EvalsToInTime.trans (TM2.step program)
        1 1 (scanHorizontalCfg data)
        (moveHorizontalCfg (inputState .unit) afterScan)
        (some (scanHorizontalCfg nextData))
        (by simpa [afterScan] using scanned)
        (by simpa [nextData] using moved)
      have remaining := induction nextData
        (by simp [nextData, afterScan, remainingInput])
        (by simp [nextData])
      have whole := EvalsToInTime.trans (TM2.step program)
        2 (2 * word.length)
        (scanHorizontalCfg data) (scanHorizontalCfg nextData)
        (some (scanHorizontalCfg
          { nextData with
            input := rest
            horizontal := word.reverse ++ nextData.horizontal
            horizontalComplement := complementRest }))
        (by simpa using firstTwo) remaining
      convert whole using 1
      · simp [nextData, afterScan, List.reverse_cons, List.append_assoc]
      · simp
        omega

/-- Consume the horizontal delimiter and discard the one reserved
complement unit. -/
def finishHorizontal_evalsInTime (complementRest : List Unit)
    (rest : List InputToken) (data : TapeData)
    (inputEq : data.input = .horizontalEnd :: rest)
    (complementEq : data.horizontalComplement = () :: complementRest) :
    EvalsToInTime (TM2.step program)
      (scanHorizontalCfg data)
      (some (scanVerticalCfg
        { data with
          input := rest
          horizontalComplement := complementRest }))
      2 := by
  let afterScan : TapeData := { data with input := rest }
  have scanned := oneStep
    (step_scanHorizontal_horizontalEnd data rest inputEq)
  have reserved := oneStep (step_reserveComplement_cons
    afterScan complementRest (by
      simp [afterScan, complementEq]))
  have whole := EvalsToInTime.trans (TM2.step program)
    1 1 (scanHorizontalCfg data)
    (reserveComplementCfg (inputState .horizontalEnd) afterScan)
    (some (scanVerticalCfg
      { afterScan with horizontalComplement := complementRest }))
    (by simpa [afterScan] using scanned) reserved
  simpa [afterScan] using whole

/-- Consume a unary vertical field and enter color parsing. -/
def scanVerticalUnits_evalsInTime (word : List Unit)
    (rest : List InputToken) (data : TapeData)
    (inputEq : data.input =
      List.replicate word.length .unit ++ .verticalEnd :: rest) :
    EvalsToInTime (TM2.step program)
      (scanVerticalCfg data)
      (some (scanColorCfg
        { data with
          input := rest
          verticalPositive := word.reverse ++ data.verticalPositive }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_scanVertical_verticalEnd data rest (by
        simpa using inputEq))
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let remainingInput :=
        List.replicate word.length
          GadgetSparseRouteRasterNormalizedTokens.Token.unit ++
            .verticalEnd :: rest
      let nextData : TapeData :=
        { data with
          input := remainingInput
          verticalPositive := () :: data.verticalPositive }
      have first := oneStep (step_scanVertical_unit data remainingInput (by
        simpa [remainingInput, List.replicate_succ] using inputEq))
      have remaining := induction nextData (by simp [nextData, remainingInput])
      have whole := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (scanVerticalCfg data) (scanVerticalCfg nextData)
        (some (scanColorCfg
          { nextData with
            input := rest
            verticalPositive := word.reverse ++
              nextData.verticalPositive })) first remaining
      convert whole using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
