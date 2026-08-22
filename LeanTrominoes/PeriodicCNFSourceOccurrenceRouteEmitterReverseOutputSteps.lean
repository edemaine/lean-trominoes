/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOutputTapeUpdates

/-! # Output-reversal scan steps for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_reverseOutput_nil (cursor : Cursor) (data : TapeData)
    (outputReverseEq : data.outputReverse = []) :
    machine.step (reverseOutputCfg cursor data) =
      some (cleanupCfg .input cursor { data with outputReverse := [] }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
    cleanupCfg, cursorCfg, cfg, program, TM2.stepAux, tapes,
    List.head?_nil, List.tail_nil, outputIsNone, cursorFromState,
    clear, update_tapes_outputReverse]
  rfl

theorem step_reverseOutput_cons (cursor : Cursor) (data : TapeData)
    (token : OutputToken) (remaining : List OutputToken)
    (outputReverseEq : data.outputReverse = token :: remaining) :
    machine.step (reverseOutputCfg cursor data) =
      some (pushOutputCfg cursor token
        { data with outputReverse := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change outputReverse = token :: remaining at outputReverseEq
  subst outputReverse
  simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
    pushOutputCfg, outputCfg, cursorCfg, cfg, program, TM2.stepAux,
    tapes, List.head?_cons, List.tail_cons, outputIsNone,
    cursorFromState, update_tapes_outputReverse]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
