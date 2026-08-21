/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterScan
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterCounterSteps

/-! # First-counter execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def scanFirst_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride)
    (word : List Unit) (data : TapeData Data)
    (firstEq : data.first = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (scanFirstCfg index data)
      (some (restoreFirstCfg index
        { data with
          first := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate (firstStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanFirst_nil firstSelected secondSelected positionSelected
          recipes ending index data firstEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          first := word
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate firstStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanFirst_cons_atom firstSelected secondSelected
          positionSelected recipes ending index base firstStride
          secondStride positionStride data word firstEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (scanFirstCfg index data)
        (scanFirstCfg index nextData)
        (some (restoreFirstCfg index
          { nextData with
            first := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate (firstStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show firstStride * (word.length + 1) =
            firstStride * word.length + firstStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restoreFirst_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (restoreFirstCfg index data)
      (some (scanSecondCfg index
        { data with
          first := word.reverse ++ data.first
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreFirst_nil firstSelected secondSelected positionSelected
          recipes ending index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          first := () :: data.first
          scratch := word }
      have firstStep := oneStep
        (step_restoreFirst_cons firstSelected secondSelected positionSelected
          recipes ending index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (restoreFirstCfg index data)
        (restoreFirstCfg index nextData)
        (some (scanSecondCfg index
          { nextData with
            first := word.reverse ++ nextData.first
            scratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
