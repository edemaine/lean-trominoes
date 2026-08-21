/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecutionData

/-! # Scan and template-emission execution -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def prefix_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (scanCfg (initialData workspace))
      (some (clearFirstCfg
        (endedData firstSelected secondSelected positionSelected recipes ending
          workspace)))
      (prefixTime firstSelected secondSelected positionSelected recipes
        workspace) := by
  have scanRun := scan_evalsInTime firstSelected secondSelected
    positionSelected recipes ending workspace (initialData workspace) rfl
  have positionsRun := positions_evalsInTime firstSelected secondSelected
    positionSelected recipes ending
    (firstCountOf firstSelected workspace)
    (secondCountOf secondSelected workspace) 0
    (positionCountOf positionSelected workspace)
    (scannedData firstSelected secondSelected positionSelected workspace)
    rfl rfl rfl rfl rfl
  have firstTwo := EvalsToInTime.trans
    (TM2.step
      (program firstSelected secondSelected positionSelected recipes ending))
    (workspace.length + 1)
    (positionRangeTime recipes
      (firstCountOf firstSelected workspace)
      (secondCountOf secondSelected workspace) 0
      (positionCountOf positionSelected workspace))
    (scanCfg (initialData workspace))
    (beginPositionCfg
      (scannedData firstSelected secondSelected positionSelected workspace))
    (some (emitEndingCfg
      (positionedData firstSelected secondSelected positionSelected recipes
        workspace)))
    (by
      simpa [initialData, scannedData, firstCountOf, secondCountOf,
        positionCountOf] using scanRun)
    (by
      simpa [scannedData, positionedData, emittedOf] using positionsRun)
  have endingRun := oneStep
    (step_emitEnding firstSelected secondSelected positionSelected recipes
      ending
      (positionedData firstSelected secondSelected positionSelected recipes
        workspace))
  have all := EvalsToInTime.trans
    (TM2.step
      (program firstSelected secondSelected positionSelected recipes ending))
    (positionRangeTime recipes
      (firstCountOf firstSelected workspace)
      (secondCountOf secondSelected workspace) 0
      (positionCountOf positionSelected workspace) +
        (workspace.length + 1))
    1
    (scanCfg (initialData workspace))
    (emitEndingCfg
      (positionedData firstSelected secondSelected positionSelected recipes
        workspace))
    (some (clearFirstCfg
      (endedData firstSelected secondSelected positionSelected recipes ending
        workspace)))
    firstTwo
    (by
      simpa [endedData, positionedData, List.append_assoc] using endingRun)
  convert all using 1
  simp [prefixTime]
  omega

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
