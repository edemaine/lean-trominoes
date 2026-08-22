/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupSteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport

/-! # Execution of one final cleanup stage -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def cleanupStage_evalsInTime (stage : CleanupStage)
    (cursor : Cursor) (symbols : List (Alphabet stage.stack))
    (data : TapeData) (symbolsEq : stage.symbols data = symbols) :
    EvalsToInTime machine.step (cleanupCfg stage cursor data)
      (some (stage.afterCfg cursor data)) (symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := oneStep (step_cleanup_nil stage cursor data symbolsEq)
      simpa using step
  | cons token symbols induction =>
      let nextData := stage.set data symbols
      have first := oneStep
        (step_cleanup_cons stage cursor data token symbols symbolsEq)
      have rest := induction nextData (by simp [nextData])
      have whole := EvalsToInTime.trans machine.step 1
        (symbols.length + 1)
        (cleanupCfg stage cursor data)
        (cleanupCfg stage cursor nextData)
        (some (stage.afterCfg cursor nextData)) first rest
      cases stage <;>
        simpa [nextData, CleanupStage.afterCfg, CleanupStage.cleared,
          CleanupStage.set, Nat.add_assoc] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
