/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecutionPrefix
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecutionCleanup
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecutionInterface

/-! # Exact execution of the trivariate template emitter -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def machine_outputsInTime {Data : Type} [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    TM2OutputsInTime
      (machine Data firstSelected secondSelected positionSelected
        recipes ending)
      workspace
      (some (emittedOutput firstSelected secondSelected positionSelected
        recipes ending workspace))
      (totalTime firstSelected secondSelected positionSelected
        recipes ending workspace) := by
  have prefixRun := prefix_evalsInTime firstSelected secondSelected
    positionSelected recipes ending workspace
  have cleanupRun := cleanup_evalsInTime firstSelected secondSelected
    positionSelected recipes ending workspace
  have beforeReverse := EvalsToInTime.trans
    (TM2.step
      (program firstSelected secondSelected positionSelected recipes ending))
    (prefixTime firstSelected secondSelected positionSelected recipes workspace)
    (cleanupTime firstSelected secondSelected positionSelected workspace)
    (scanCfg (initialData workspace))
    (clearFirstCfg
      (endedData firstSelected secondSelected positionSelected recipes ending
        workspace))
    (some (reverseOutputCfg
      (clearedData firstSelected secondSelected positionSelected recipes ending
        workspace)))
    prefixRun cleanupRun
  have outputReverseEq :
      (clearedData firstSelected secondSelected positionSelected recipes ending
        workspace).outputReverse =
      (emittedOutput firstSelected secondSelected positionSelected recipes
        ending workspace).reverse := by
    simpa [clearedData, secondClearedData, firstClearedData] using
      endedData_outputReverse firstSelected secondSelected positionSelected
        recipes ending workspace
  have reverseRun := reverseOutput_evalsInTime firstSelected secondSelected
    positionSelected recipes ending
    (emittedOutput firstSelected secondSelected positionSelected recipes ending
      workspace).reverse
    (clearedData firstSelected secondSelected positionSelected recipes ending
      workspace)
    outputReverseEq
  have whole := EvalsToInTime.trans
    (TM2.step
      (program firstSelected secondSelected positionSelected recipes ending))
    (cleanupTime firstSelected secondSelected positionSelected workspace +
      prefixTime firstSelected secondSelected positionSelected recipes
        workspace)
    ((emittedOutput firstSelected secondSelected positionSelected recipes ending
      workspace).length + 1)
    (scanCfg (initialData workspace))
    (reverseOutputCfg
      (clearedData firstSelected secondSelected positionSelected recipes ending
        workspace))
    (some (haltCfg
      (emittedOutput firstSelected secondSelected positionSelected recipes
        ending workspace)))
    beforeReverse
    (by
      simpa [clearedData, secondClearedData, firstClearedData, endedData,
        positionedData, initialData, haltDataCfg, haltCfg] using reverseRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind
        (TM2.step
          (program firstSelected secondSelected positionSelected recipes
            ending)))^[whole.steps]
        (some (initList
          (machine Data firstSelected secondSelected positionSelected recipes
            ending)
          workspace)) =
          some (haltList
            (machine Data firstSelected secondSelected positionSelected recipes
              ending)
            (emittedOutput firstSelected secondSelected positionSelected recipes
              ending workspace))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime]
      omega)

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
