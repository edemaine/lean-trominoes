/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOccurrenceSteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # Occurrence-scan boundary steps -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem step_scanData_literalEnd (base : TapeData) (state : ScanState)
    (tokens : List SourceOccurrenceRouteTokens.Token) :
    machine.step (scanOccurrencesCfg state.cursor
        (scanData base state (.literalEnd :: tokens))) =
      some (scanOccurrencesCfg state.cursor (scanData base state tokens)) := by
  have step := step_scanOccurrences_literalEnd state.cursor
    (scanData base state (.literalEnd :: tokens)) tokens rfl
  simpa only [scanData] using step

theorem step_scanData_nil (base : TapeData) (state : ScanState) :
    machine.step (scanOccurrencesCfg state.cursor
        (scanData base state [])) =
      some (reverseOutputCfg state.cursor (scanData base state [])) := by
  have step := step_scanOccurrences_nil state.cursor
    (scanData base state []) rfl
  simpa only [scanData] using step

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
