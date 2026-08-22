/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOutputTapeUpdates

/-! # Target-delimiter step for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_scanTarget_delimiter (cursor : Cursor) (data : TapeData)
    (remaining : List UnarySymbol)
    (targetsEq : data.targets = .delimiter :: remaining) :
    machine.step (scanTargetCfg cursor data) =
      some (finishRecordCfg cursor.literalIndex cursor.currentNext
        cursor.anchorValue cursor
        { data with
          targets := remaining
          outputReverse := .atomEnd :: data.outputReverse }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change targets = .delimiter :: remaining at targetsEq
  subst targets
  simp only [FinTM2.step, TM2.step, machine, scanTargetCfg,
    finishRecordCfg, cursorCfg, cfg, program, TM2.stepAux, tapes,
    List.head?_cons, List.tail_cons, unaryIsNone, unaryIsUnit,
    cursorFromState, clear, Cursor.anchorValue, update_tapes_targets,
    update_tapes_outputReverse]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
