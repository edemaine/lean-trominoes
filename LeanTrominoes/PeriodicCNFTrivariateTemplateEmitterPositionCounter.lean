/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterScan
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterCounterSteps

/-! # Position-counter execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def scanPosition_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (scanPositionCfg index data)
      (some (restorePositionCfg index
        { data with
          processed := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate (positionStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanPosition_nil firstSelected secondSelected positionSelected
          recipes ending index data processedEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := word
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate positionStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanPosition_cons_atom firstSelected secondSelected
          positionSelected recipes ending index base firstStride
          secondStride positionStride data word processedEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (scanPositionCfg index data)
        (scanPositionCfg index nextData)
        (some (restorePositionCfg index
          { nextData with
            processed := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate (positionStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show positionStride * (word.length + 1) =
            positionStride * word.length + positionStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restorePosition_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (restorePositionCfg index data)
      (some (afterRecipeCfg recipes index
        { data with
          processed := word.reverse ++ data.processed
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restorePosition_nil firstSelected secondSelected
          positionSelected recipes ending index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := () :: data.processed
          scratch := word }
      have firstStep := oneStep
        (step_restorePosition_cons firstSelected secondSelected
          positionSelected recipes ending index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (restorePositionCfg index data)
        (restorePositionCfg index nextData)
        (some (afterRecipeCfg recipes index
          { nextData with
            processed := word.reverse ++ nextData.processed
            scratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
