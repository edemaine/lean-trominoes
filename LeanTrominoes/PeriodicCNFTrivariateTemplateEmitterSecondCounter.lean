/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterScan
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterCounterSteps

/-! # Second-counter execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def scanSecond_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride)
    (word : List Unit) (data : TapeData Data)
    (secondEq : data.second = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (scanSecondCfg index data)
      (some (restoreSecondCfg index
        { data with
          second := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate (secondStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanSecond_nil firstSelected secondSelected positionSelected
          recipes ending index data secondEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          second := word
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanSecond_cons_atom firstSelected secondSelected
          positionSelected recipes ending index base firstStride
          secondStride positionStride data word secondEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (scanSecondCfg index data)
        (scanSecondCfg index nextData)
        (some (restoreSecondCfg index
          { nextData with
            second := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate (secondStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show secondStride * (word.length + 1) =
            secondStride * word.length + secondStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restoreSecond_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (restoreSecondCfg index data)
      (some (scanPositionCfg index
        { data with
          second := word.reverse ++ data.second
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreSecond_nil firstSelected secondSelected positionSelected
          recipes ending index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          second := () :: data.second
          scratch := word }
      have firstStep := oneStep
        (step_restoreSecond_cons firstSelected secondSelected positionSelected
          recipes ending index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (restoreSecondCfg index data)
        (restoreSecondCfg index nextData)
        (some (scanPositionCfg index
          { nextData with
            second := word.reverse ++ nextData.second
            scratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
