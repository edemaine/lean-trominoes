/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterRecipeStep

/-!
# Complete outer-recipe execution of the triangular emitter

The entry step and the verified persistent/outer counter pairs are composed
into one exact theorem for either outer template stage.  All counters and
scratch stacks are restored, the precise bivariate recipe token word is
prepended to the reverse output, and the execution time is explicit.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

theorem heldOffset_eq_zero_of_not_inner {Data : Type}
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (notInner : stage.isInner = false) :
    heldOffset parameters stage index = 0 := by
  cases stage <;> simp_all [heldOffset]

theorem afterPositionCfg_eq_afterRecipe_of_not_inner {Data : Type}
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (notInner : stage.isInner = false) :
    parameters.afterPositionCfg stage index data =
      parameters.afterRecipeCfg stage index data := by
  cases stage <;> simp_all [Parameters.afterPositionCfg]

def outerRecipeTime (first position : Nat) : Recipe → Nat
  | .fixed _ => 1
  | .atom _ _ _ => 2 * first + 2 * position + 5

/-- Execute one complete recipe in either non-inner stage. -/
def executeOuterRecipe_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (notInner : stage.isInner = false)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (first position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate position ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.executeCfg stage index data)
      (some (parameters.afterRecipeCfg stage index
        { data with
          first := List.replicate first ()
          processed := List.replicate position ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((BivariateProgramTemplates.Recipe.tokens first position
                (recipeAt parameters.outerFirst parameters.inner
                  parameters.outerSecond stage index)).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (outerRecipeTime first position
        (recipeAt parameters.outerFirst parameters.inner
          parameters.outerSecond stage index)) := by
  cases recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index with
  | fixed token =>
      have step := oneStep
        (step_execute_fixed parameters stage index token data recipeEq)
      convert step using 1 <;>
        simp [BivariateProgramTemplates.Recipe.tokens, outerRecipeTime,
          firstEq, processedEq, firstScratchEq, positionScratchEq]
  | atom base firstStride secondStride =>
      let emittedData : TapeData Data :=
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have executed := oneStep
        (step_execute_atom parameters stage index base firstStride
          secondStride data recipeEq)
      have scannedFirst := scanFirst_evalsInTime parameters stage index
        base firstStride secondStride recipeEq
        (List.replicate first ()) emittedData (by
          simpa [emittedData] using firstEq)
      let firstScannedData : TapeData Data :=
        { emittedData with
          first := []
          firstScratch := (List.replicate first ()).reverse
          outputReverse :=
            List.replicate (firstStride * first)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              emittedData.outputReverse }
      have executedAndScanned := EvalsToInTime.trans parameters.transition
        1 (first + 1)
        (parameters.executeCfg stage index data)
        (parameters.scanFirstCfg stage index emittedData)
        (some (parameters.restoreFirstCfg stage index firstScannedData))
        executed (by
          simpa [firstScannedData, emittedData, firstScratchEq]
            using scannedFirst)
      have restoredFirst := restoreFirst_evalsInTime parameters stage index
        (List.replicate first ()).reverse firstScannedData rfl
      let firstRestoredData : TapeData Data :=
        { firstScannedData with
          first := List.replicate first ()
          firstScratch := [] }
      have throughFirstRaw := EvalsToInTime.trans parameters.transition
        (first + 2) (first + 1)
        (parameters.executeCfg stage index data)
        (parameters.restoreFirstCfg stage index firstScannedData)
        (some (parameters.scanPositionCfg stage index firstRestoredData))
        executedAndScanned (by
          have offset := heldOffset_eq_zero_of_not_inner
            parameters stage index notInner
          convert restoredFirst using 1 <;>
            simp [firstRestoredData, firstScannedData, offset])
      have throughFirst : EvalsToInTime parameters.transition
          (parameters.executeCfg stage index data)
          (some (parameters.scanPositionCfg stage index firstRestoredData))
          (2 * first + 3) := by
        convert throughFirstRaw using 1
        all_goals omega
      have scannedPosition := scanPosition_evalsInTime parameters stage index
        base firstStride secondStride recipeEq
        (List.replicate position ()) firstRestoredData (by
          simpa [firstRestoredData, firstScannedData, emittedData]
            using processedEq)
      let positionScannedData : TapeData Data :=
        { firstRestoredData with
          processed := []
          positionScratch := (List.replicate position ()).reverse
          outputReverse :=
            List.replicate (secondStride * position)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              firstRestoredData.outputReverse }
      have throughPositionScanRaw := EvalsToInTime.trans
        parameters.transition (2 * first + 3) (position + 1)
        (parameters.executeCfg stage index data)
        (parameters.scanPositionCfg stage index firstRestoredData)
        (some (parameters.restorePositionCfg stage index
          positionScannedData)) throughFirst (by
            simpa [positionScannedData, firstRestoredData,
              firstScannedData, emittedData, positionScratchEq]
              using scannedPosition)
      have throughPositionScan : EvalsToInTime parameters.transition
          (parameters.executeCfg stage index data)
          (some (parameters.restorePositionCfg stage index
            positionScannedData))
          (2 * first + position + 4) := by
        convert throughPositionScanRaw using 1
        all_goals omega
      have restoredPosition := restorePosition_evalsInTime parameters stage
        index (List.replicate position ()).reverse positionScannedData rfl
      have whole := EvalsToInTime.trans parameters.transition
        (2 * first + position + 4) (position + 1)
        (parameters.executeCfg stage index data)
        (parameters.restorePositionCfg stage index positionScannedData)
        (some (parameters.afterRecipeCfg stage index
          { data with
            first := List.replicate first ()
            processed := List.replicate position ()
            firstScratch := []
            positionScratch := []
            outputReverse :=
              List.replicate
                  (base + firstStride * first + secondStride * position)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                data.outputReverse }))
        throughPositionScan (by
          have outputEq :
              List.replicate
                    (base + firstStride * first + secondStride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  data.outputReverse =
                List.replicate (secondStride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  (List.replicate (firstStride * first)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                    (List.replicate base
                      (Sum.inr Token.atomUnit : Workspace Data) ++
                      data.outputReverse)) := by
            rw [← List.append_assoc, ← List.append_assoc,
              ← List.replicate_add, ← List.replicate_add]
            congr 2
            ring
          have destination := afterPositionCfg_eq_afterRecipe_of_not_inner
            parameters stage index
              { positionScannedData with
                processed :=
                  (List.replicate position ()).reverse.reverse ++
                    positionScannedData.processed
                positionScratch := [] }
              notInner
          rw [destination] at restoredPosition
          convert restoredPosition using 1
          · simp [positionScannedData, firstRestoredData, firstScannedData,
              emittedData, outputEq]
          · simp)
      convert whole using 1
      · simp [BivariateProgramTemplates.Recipe.tokens]
      · simp [outerRecipeTime]
        ring

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
