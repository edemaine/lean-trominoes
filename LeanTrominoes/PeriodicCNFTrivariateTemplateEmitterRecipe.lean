/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterBoundarySteps
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterFirstCounter
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterSecondCounter
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterPositionCounter

/-! # Exact recipe execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens
open TrivariateTemplateEmitter

def recipeTime (first second position : Nat) : Recipe → Nat
  | .fixed _ => 1
  | .atom _ _ _ _ => 2 * first + 2 * second + 2 * position + 7

def executeRecipe_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (first second position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (secondEq : data.second = List.replicate second ())
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (executeCfg index data)
      (some (afterRecipeCfg recipes index
        { data with
          first := List.replicate first ()
          second := List.replicate second ()
          processed := List.replicate position ()
          scratch := []
          outputReverse :=
            ((Recipe.tokens first second position
                (recipes.get index)).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (recipeTime first second position (recipes.get index)) := by
  cases recipeEq : recipes.get index with
  | fixed token =>
      have step := oneStep
        (step_execute_fixed firstSelected secondSelected positionSelected
          recipes ending index token data recipeEq)
      convert step using 1 <;>
        simp [Recipe.tokens, recipeTime, firstEq, secondEq,
          processedEq, scratchEq]
  | atom base firstStride secondStride positionStride =>
      let emittedData : TapeData Data :=
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have executed := oneStep
        (step_execute_atom firstSelected secondSelected positionSelected
          recipes ending index base firstStride secondStride positionStride
          data recipeEq)
      have scannedFirst := scanFirst_evalsInTime firstSelected secondSelected
        positionSelected recipes ending index base firstStride secondStride
        positionStride recipeEq (List.replicate first ()) emittedData (by
          simpa [emittedData] using firstEq)
      let firstScannedData : TapeData Data :=
        { emittedData with
          first := []
          scratch := (List.replicate first ()).reverse
          outputReverse :=
            List.replicate (firstStride * first)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              emittedData.outputReverse }
      have executedAndScanned := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (first + 1) (executeCfg index data)
        (scanFirstCfg index emittedData)
        (some (restoreFirstCfg index firstScannedData)) executed (by
          simpa [firstScannedData, emittedData, scratchEq] using scannedFirst)
      have restoredFirst := restoreFirst_evalsInTime firstSelected
        secondSelected positionSelected recipes ending index
        (List.replicate first ()).reverse firstScannedData rfl
      let firstRestoredData : TapeData Data :=
        { firstScannedData with
          first := List.replicate first ()
          scratch := [] }
      have throughFirstRaw := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (first + 2) (first + 1) (executeCfg index data)
        (restoreFirstCfg index firstScannedData)
        (some (scanSecondCfg index firstRestoredData)) executedAndScanned
        (by
          convert restoredFirst using 1 <;>
            simp [firstRestoredData, firstScannedData])
      have throughFirst : EvalsToInTime
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          (executeCfg index data)
          (some (scanSecondCfg index firstRestoredData))
          (2 * first + 3) := by
        convert throughFirstRaw using 1
        all_goals omega
      have scannedSecond := scanSecond_evalsInTime firstSelected
        secondSelected positionSelected recipes ending index base
        firstStride secondStride positionStride recipeEq
        (List.replicate second ()) firstRestoredData (by
          simpa [firstRestoredData, firstScannedData, emittedData]
            using secondEq)
      let secondScannedData : TapeData Data :=
        { firstRestoredData with
          second := []
          scratch := (List.replicate second ()).reverse
          outputReverse :=
            List.replicate (secondStride * second)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              firstRestoredData.outputReverse }
      have throughSecondScanRaw := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (2 * first + 3) (second + 1) (executeCfg index data)
        (scanSecondCfg index firstRestoredData)
        (some (restoreSecondCfg index secondScannedData)) throughFirst (by
          simpa [secondScannedData, firstRestoredData, firstScannedData,
            emittedData, scratchEq] using scannedSecond)
      have throughSecondScan : EvalsToInTime
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          (executeCfg index data)
          (some (restoreSecondCfg index secondScannedData))
          (2 * first + second + 4) := by
        convert throughSecondScanRaw using 1
        all_goals omega
      have restoredSecond := restoreSecond_evalsInTime firstSelected
        secondSelected positionSelected recipes ending index
        (List.replicate second ()).reverse secondScannedData rfl
      let secondRestoredData : TapeData Data :=
        { secondScannedData with
          second := List.replicate second ()
          scratch := [] }
      have throughSecondRaw := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (2 * first + second + 4) (second + 1) (executeCfg index data)
        (restoreSecondCfg index secondScannedData)
        (some (scanPositionCfg index secondRestoredData)) throughSecondScan
        (by
          convert restoredSecond using 1 <;>
            simp [secondRestoredData, secondScannedData])
      have throughSecond : EvalsToInTime
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          (executeCfg index data)
          (some (scanPositionCfg index secondRestoredData))
          (2 * first + 2 * second + 5) := by
        convert throughSecondRaw using 1
        all_goals omega
      have scannedPosition := scanPosition_evalsInTime firstSelected
        secondSelected positionSelected recipes ending index base
        firstStride secondStride positionStride recipeEq
        (List.replicate position ()) secondRestoredData (by
          simpa [secondRestoredData, secondScannedData, firstRestoredData,
            firstScannedData, emittedData] using processedEq)
      let positionScannedData : TapeData Data :=
        { secondRestoredData with
          processed := []
          scratch := (List.replicate position ()).reverse
          outputReverse :=
            List.replicate (positionStride * position)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              secondRestoredData.outputReverse }
      have throughPositionScanRaw := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (2 * first + 2 * second + 5) (position + 1)
        (executeCfg index data) (scanPositionCfg index secondRestoredData)
        (some (restorePositionCfg index positionScannedData)) throughSecond
        (by
          simpa [positionScannedData, secondRestoredData, secondScannedData,
            firstRestoredData, firstScannedData, emittedData, scratchEq]
            using scannedPosition)
      have throughPositionScan : EvalsToInTime
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          (executeCfg index data)
          (some (restorePositionCfg index positionScannedData))
          (2 * first + 2 * second + position + 6) := by
        convert throughPositionScanRaw using 1
        all_goals omega
      have restoredPosition := restorePosition_evalsInTime firstSelected
        secondSelected positionSelected recipes ending index
        (List.replicate position ()).reverse positionScannedData rfl
      have whole := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (2 * first + 2 * second + position + 6) (position + 1)
        (executeCfg index data) (restorePositionCfg index positionScannedData)
        (some (afterRecipeCfg recipes index
          { data with
            first := List.replicate first ()
            second := List.replicate second ()
            processed := List.replicate position ()
            scratch := []
            outputReverse :=
              List.replicate
                  (base + firstStride * first + secondStride * second +
                    positionStride * position)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                data.outputReverse }))
        throughPositionScan (by
          have outputEq :
              List.replicate
                    (base + firstStride * first + secondStride * second +
                      positionStride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  data.outputReverse =
                List.replicate (positionStride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  (List.replicate (secondStride * second)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                    (List.replicate (firstStride * first)
                      (Sum.inr Token.atomUnit : Workspace Data) ++
                      (List.replicate base
                        (Sum.inr Token.atomUnit : Workspace Data) ++
                        data.outputReverse))) := by
            rw [← List.append_assoc, ← List.append_assoc,
              ← List.append_assoc, ← List.replicate_add,
              ← List.replicate_add, ← List.replicate_add]
            congr 2
            ring
          convert restoredPosition using 1
          · simp [positionScannedData, secondRestoredData,
              secondScannedData, firstRestoredData, firstScannedData,
              emittedData, outputEq]
          · simp)
      convert whole using 1
      · simp [Recipe.tokens]
      · simp [recipeTime]
        ring

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
