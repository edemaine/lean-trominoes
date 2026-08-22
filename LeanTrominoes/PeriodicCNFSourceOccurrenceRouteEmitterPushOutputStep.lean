/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOutputTapeUpdates

/-! # Output-push step for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_pushOutput (cursor : Cursor) (data : TapeData)
    (token : OutputToken) :
    machine.step (pushOutputCfg cursor token data) =
      some (reverseOutputCfg cursor
        { data with output := token :: data.output }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, pushOutputCfg,
    reverseOutputCfg, outputCfg, cursorCfg, cfg, program, TM2.stepAux,
    outputFromState, cursorFromState, clear, update_tapes_output]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
