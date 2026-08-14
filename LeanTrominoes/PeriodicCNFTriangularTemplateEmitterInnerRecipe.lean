/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterRecipe

/-!
# Complete inner-recipe execution of the triangular emitter

An inner atom position is the completed outer count, plus the held current
marker, plus the completed inner count.  This file composes all three verified
counter pairs and proves the resulting exact affine token run and runtime.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

theorem heldOffset_inner_atom {Data : Type} (parameters : Parameters Data)
    (index : Fin parameters.inner.length) (base firstStride secondStride : Nat)
    (recipeEq : parameters.inner.get index =
      .atom base firstStride secondStride) :
    heldOffset parameters .inner index = secondStride := by
  have atEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond .inner index =
        .atom base firstStride secondStride := by
    simpa [recipeAt, stageRecipes, stageCount] using recipeEq
  unfold heldOffset
  simp only [Stage.isInner, if_true]
  rw [atEq]

def innerRecipeTime (first outer inner : Nat) : Recipe → Nat
  | .fixed _ => 1
  | .atom _ _ _ => 2 * first + 2 * outer + 2 * inner + 7

/-- Execute one complete inner-stage recipe. -/
def executeInnerRecipe_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (first outer innerCount : Nat) (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate outer ())
    (innerEq : data.innerProcessed = List.replicate innerCount ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.executeCfg .inner index data)
      (some (parameters.afterRecipeCfg .inner index
        { data with
          first := List.replicate first ()
          processed := List.replicate outer ()
          innerProcessed := List.replicate innerCount ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((BivariateProgramTemplates.Recipe.tokens first
                (outer + 1 + innerCount) (parameters.inner.get index)).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (innerRecipeTime first outer innerCount
        (parameters.inner.get index)) := by
  cases recipeEq : parameters.inner.get index with
  | fixed token =>
      have step := oneStep
        (step_execute_fixed parameters .inner index token data (by
          simpa [recipeAt, stageRecipes, stageCount] using recipeEq))
      convert step using 1 <;>
        simp [BivariateProgramTemplates.Recipe.tokens, innerRecipeTime,
          firstEq, processedEq, innerEq, firstScratchEq,
          positionScratchEq]
  | atom base firstStride secondStride =>
      have recipeAtEq : recipeAt parameters.outerFirst parameters.inner
          parameters.outerSecond .inner index =
          .atom base firstStride secondStride := by
        simpa [recipeAt, stageRecipes, stageCount] using recipeEq
      let emittedData : TapeData Data :=
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have executed := oneStep
        (step_execute_atom parameters .inner index base firstStride
          secondStride data recipeAtEq)
      have scannedFirst := scanFirst_evalsInTime parameters .inner index
        base firstStride secondStride recipeAtEq
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
        (parameters.executeCfg .inner index data)
        (parameters.scanFirstCfg .inner index emittedData)
        (some (parameters.restoreFirstCfg .inner index firstScannedData))
        executed (by
          simpa [firstScannedData, emittedData, firstScratchEq]
            using scannedFirst)
      have restoredFirst := restoreFirst_evalsInTime parameters .inner index
        (List.replicate first ()).reverse firstScannedData rfl
      let firstRestoredData : TapeData Data :=
        { firstScannedData with
          first := List.replicate first ()
          firstScratch := []
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              firstScannedData.outputReverse }
      have throughFirstRaw := EvalsToInTime.trans parameters.transition
        (first + 2) (first + 1)
        (parameters.executeCfg .inner index data)
        (parameters.restoreFirstCfg .inner index firstScannedData)
        (some (parameters.scanPositionCfg .inner index firstRestoredData))
        executedAndScanned (by
          have offset := heldOffset_inner_atom parameters index base
            firstStride secondStride recipeEq
          convert restoredFirst using 1 <;>
            simp [firstRestoredData, firstScannedData, offset])
      have throughFirst : EvalsToInTime parameters.transition
          (parameters.executeCfg .inner index data)
          (some (parameters.scanPositionCfg .inner index firstRestoredData))
          (2 * first + 3) := by
        convert throughFirstRaw using 1
        all_goals omega
      have scannedOuter := scanPosition_evalsInTime parameters .inner index
        base firstStride secondStride recipeAtEq
        (List.replicate outer ()) firstRestoredData (by
          simpa [firstRestoredData, firstScannedData, emittedData]
            using processedEq)
      let outerScannedData : TapeData Data :=
        { firstRestoredData with
          processed := []
          positionScratch := (List.replicate outer ()).reverse
          outputReverse :=
            List.replicate (secondStride * outer)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              firstRestoredData.outputReverse }
      have throughOuterScanRaw := EvalsToInTime.trans parameters.transition
        (2 * first + 3) (outer + 1)
        (parameters.executeCfg .inner index data)
        (parameters.scanPositionCfg .inner index firstRestoredData)
        (some (parameters.restorePositionCfg .inner index outerScannedData))
        throughFirst (by
          simpa [outerScannedData, firstRestoredData, firstScannedData,
            emittedData, positionScratchEq] using scannedOuter)
      have throughOuterScan : EvalsToInTime parameters.transition
          (parameters.executeCfg .inner index data)
          (some (parameters.restorePositionCfg .inner index outerScannedData))
          (2 * first + outer + 4) := by
        convert throughOuterScanRaw using 1
        all_goals omega
      have restoredOuter := restorePosition_evalsInTime parameters .inner
        index (List.replicate outer ()).reverse outerScannedData rfl
      let outerRestoredData : TapeData Data :=
        { outerScannedData with
          processed := List.replicate outer ()
          positionScratch := [] }
      have throughOuterRaw := EvalsToInTime.trans parameters.transition
        (2 * first + outer + 4) (outer + 1)
        (parameters.executeCfg .inner index data)
        (parameters.restorePositionCfg .inner index outerScannedData)
        (some (parameters.scanInnerCfg index outerRestoredData))
        throughOuterScan (by
          convert restoredOuter using 1 <;>
            simp [Parameters.afterPositionCfg, outerRestoredData,
              outerScannedData])
      have throughOuter : EvalsToInTime parameters.transition
          (parameters.executeCfg .inner index data)
          (some (parameters.scanInnerCfg index outerRestoredData))
          (2 * first + 2 * outer + 5) := by
        convert throughOuterRaw using 1
        all_goals omega
      have scannedInner := scanInner_evalsInTime parameters index base
        firstStride secondStride recipeEq
        (List.replicate innerCount ()) outerRestoredData (by
          simpa [outerRestoredData, outerScannedData, firstRestoredData,
            firstScannedData, emittedData] using innerEq)
      let innerScannedData : TapeData Data :=
        { outerRestoredData with
          innerProcessed := []
          positionScratch := (List.replicate innerCount ()).reverse
          outputReverse :=
            List.replicate (secondStride * innerCount)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              outerRestoredData.outputReverse }
      have throughInnerScanRaw := EvalsToInTime.trans parameters.transition
        (2 * first + 2 * outer + 5) (innerCount + 1)
        (parameters.executeCfg .inner index data)
        (parameters.scanInnerCfg index outerRestoredData)
        (some (parameters.restoreInnerCfg index innerScannedData))
        throughOuter (by
          simpa [innerScannedData, outerRestoredData, outerScannedData,
            firstRestoredData, firstScannedData, emittedData,
            positionScratchEq] using scannedInner)
      have throughInnerScan : EvalsToInTime parameters.transition
          (parameters.executeCfg .inner index data)
          (some (parameters.restoreInnerCfg index innerScannedData))
          (2 * first + 2 * outer + innerCount + 6) := by
        convert throughInnerScanRaw using 1
        all_goals omega
      have restoredInner := restoreInner_evalsInTime parameters index
        (List.replicate innerCount ()).reverse innerScannedData rfl
      have whole := EvalsToInTime.trans parameters.transition
        (2 * first + 2 * outer + innerCount + 6) (innerCount + 1)
        (parameters.executeCfg .inner index data)
        (parameters.restoreInnerCfg index innerScannedData)
        (some (parameters.afterRecipeCfg .inner index
          { data with
            first := List.replicate first ()
            processed := List.replicate outer ()
            innerProcessed := List.replicate innerCount ()
            firstScratch := []
            positionScratch := []
            outputReverse :=
              List.replicate
                  (base + firstStride * first +
                    secondStride * (outer + 1 + innerCount))
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                data.outputReverse }))
        throughInnerScan (by
          have outputEq :
              List.replicate
                    (base + firstStride * first +
                      secondStride * (outer + 1 + innerCount))
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  data.outputReverse =
                List.replicate (secondStride * innerCount)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  (List.replicate (secondStride * outer)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                    (List.replicate secondStride
                      (Sum.inr Token.atomUnit : Workspace Data) ++
                      (List.replicate (firstStride * first)
                        (Sum.inr Token.atomUnit : Workspace Data) ++
                        (List.replicate base
                          (Sum.inr Token.atomUnit : Workspace Data) ++
                          data.outputReverse)))) := by
            rw [← List.append_assoc, ← List.append_assoc,
              ← List.append_assoc, ← List.append_assoc,
              ← List.replicate_add, ← List.replicate_add,
              ← List.replicate_add, ← List.replicate_add]
            congr 2
            ring
          convert restoredInner using 1
          · simp [innerScannedData, outerRestoredData, outerScannedData,
              firstRestoredData, firstScannedData, emittedData, outputEq]
          · simp)
      convert whole using 1
      · simp [BivariateProgramTemplates.Recipe.tokens]
      · simp [innerRecipeTime]
        ring

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
