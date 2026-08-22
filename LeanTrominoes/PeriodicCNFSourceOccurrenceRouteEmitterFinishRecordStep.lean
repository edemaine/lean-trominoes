/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterPushTokens

/-! # Record-finalization step for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_finishRecord (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) (cursor : Cursor) (data : TapeData) :
    machine.step
        (finishRecordCfg literalIndex currentNext anchorNext cursor data) =
      some (scanOccurrencesCfg cursor
        { data with
          edgeIndex := () :: data.edgeIndex
          outputReverse :=
            (fixedSuffix literalIndex currentNext anchorNext).reverse ++
              data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, finishRecordCfg,
    scanOccurrencesCfg, cursorCfg, cfg, program]
  rw [stepAux_pushTokens]
  simp only [TM2.stepAux, update_tapes_edgeIndex, cursorFromState, clear]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
