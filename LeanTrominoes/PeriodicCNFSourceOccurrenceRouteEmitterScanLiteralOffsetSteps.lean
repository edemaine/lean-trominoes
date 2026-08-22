/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOccurrenceSteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # Literal and offset scan-state steps -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem step_scanData_literal (base : TapeData) (state : ScanState)
    (index : Fin 3) (tokens : List SourceOccurrenceRouteTokens.Token) :
    machine.step (scanOccurrencesCfg state.cursor
        (scanData base state (.literal index :: tokens))) =
      some (scanOccurrencesCfg (state.readLiteral index).cursor
        (scanData base (state.readLiteral index) tokens)) := by
  have step := step_scanOccurrences_literal state.cursor
    (scanData base state (.literal index :: tokens)) index tokens rfl
  simpa only [scanData, ScanState.readLiteral] using step

theorem step_scanData_offset (base : TapeData) (state : ScanState)
    (value : Bool) (tokens : List SourceOccurrenceRouteTokens.Token) :
    let next := state.readOffset base.clauseCount.length
      base.literalCount.length value
    machine.step (scanOccurrencesCfg state.cursor
        (scanData base state (.offsetNext value :: tokens))) =
      some (beginRecordCfg next.cursor (scanData base state tokens)) := by
  simp only
  have step := step_scanOccurrences_offset state.cursor
    (scanData base state (.offsetNext value :: tokens)) value tokens rfl
  simpa only [scanData, ScanState.readOffset] using step

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
