/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecutionData

/-! # Counter-cleanup execution for the trivariate emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def cleanup_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (clearFirstCfg
        (endedData firstSelected secondSelected positionSelected recipes ending
          workspace))
      (some (reverseOutputCfg
        (clearedData firstSelected secondSelected positionSelected recipes
          ending workspace)))
      (cleanupTime firstSelected secondSelected positionSelected workspace) := by
  have clearFirstRun := clearFirst_evalsInTime firstSelected secondSelected
    positionSelected recipes ending
    (List.replicate (firstCountOf firstSelected workspace) ())
    (endedData firstSelected secondSelected positionSelected recipes ending
      workspace) rfl
  have clearSecondRun := clearSecond_evalsInTime firstSelected secondSelected
    positionSelected recipes ending
    (List.replicate (secondCountOf secondSelected workspace) ())
    (firstClearedData firstSelected secondSelected positionSelected recipes
      ending workspace) rfl
  have firstTwo := EvalsToInTime.trans
    (TM2.step
      (program firstSelected secondSelected positionSelected recipes ending))
    (firstCountOf firstSelected workspace + 1)
    (secondCountOf secondSelected workspace + 1)
    (clearFirstCfg
      (endedData firstSelected secondSelected positionSelected recipes ending
        workspace))
    (clearSecondCfg
      (firstClearedData firstSelected secondSelected positionSelected recipes
        ending workspace))
    (some (clearProcessedCfg
      (secondClearedData firstSelected secondSelected positionSelected recipes
        ending workspace)))
    (by simpa [firstClearedData] using clearFirstRun)
    (by simpa [secondClearedData] using clearSecondRun)
  have clearProcessedRun := clearProcessed_evalsInTime firstSelected
    secondSelected positionSelected recipes ending
    (List.replicate (positionCountOf positionSelected workspace) ())
    (secondClearedData firstSelected secondSelected positionSelected recipes
      ending workspace) rfl
  have all := EvalsToInTime.trans
    (TM2.step
      (program firstSelected secondSelected positionSelected recipes ending))
    ((secondCountOf secondSelected workspace + 1) +
      (firstCountOf firstSelected workspace + 1))
    (positionCountOf positionSelected workspace + 1)
    (clearFirstCfg
      (endedData firstSelected secondSelected positionSelected recipes ending
        workspace))
    (clearProcessedCfg
      (secondClearedData firstSelected secondSelected positionSelected recipes
        ending workspace))
    (some (reverseOutputCfg
      (clearedData firstSelected secondSelected positionSelected recipes
        ending workspace)))
    firstTwo
    (by simpa [clearedData] using clearProcessedRun)
  convert all using 1
  simp [cleanupTime]
  omega

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
