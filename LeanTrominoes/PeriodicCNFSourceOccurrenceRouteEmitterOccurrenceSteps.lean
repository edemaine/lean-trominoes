/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOutputTapeUpdates

/-! # Occurrence-scan steps for source route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_scanOccurrences_nil (cursor : Cursor) (data : TapeData)
    (occurrencesEq : data.occurrences = []) :
    machine.step (scanOccurrencesCfg cursor data) =
      some (reverseOutputCfg cursor { data with occurrences := [] }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrences = [] at occurrencesEq
  subst occurrences
  simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
    reverseOutputCfg, cursorCfg, cfg, program, TM2.stepAux,
    occurrenceIsNone, cursorFromState, clear, update_tapes_occurrences]
  rfl

theorem step_scanOccurrences_firstClause (cursor : Cursor) (data : TapeData)
    (arity : Fin 4) (remaining : List OccurrenceToken)
    (seenEq : cursor.seenClause = false)
    (occurrencesEq : data.occurrences = .clause arity :: remaining) :
    machine.step (scanOccurrencesCfg cursor data) =
      some (scanOccurrencesCfg
        { cursor with seenClause := true, anchorNext := none }
        { data with occurrences := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrences = _ at occurrencesEq
  subst occurrences
  rcases cursor with ⟨seenClause, literalIndex, anchorNext, currentNext⟩
  change seenClause = false at seenEq
  subst seenClause
  simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
    cursorCfg, cfg, program, TM2.stepAux, occurrenceIsNone,
    occurrenceIsClause, cursorSeenClause, cursorFromState, startClause,
    update_tapes_occurrences]
  rfl

theorem step_scanOccurrences_nextClause (cursor : Cursor) (data : TapeData)
    (arity : Fin 4) (remaining : List OccurrenceToken)
    (seenEq : cursor.seenClause = true)
    (occurrencesEq : data.occurrences = .clause arity :: remaining) :
    machine.step (scanOccurrencesCfg cursor data) =
      some (scanOccurrencesCfg
        { cursor with seenClause := true, anchorNext := none }
        { data with
          occurrences := remaining
          clauseIndex := () :: data.clauseIndex }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrences = _ at occurrencesEq
  subst occurrences
  rcases cursor with ⟨seenClause, literalIndex, anchorNext, currentNext⟩
  change seenClause = true at seenEq
  subst seenClause
  simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
    cursorCfg, cfg, program, TM2.stepAux, occurrenceIsNone,
    occurrenceIsClause, cursorSeenClause, cursorFromState, startClause,
    update_tapes_occurrences, update_tapes_clauseIndex]
  rfl

theorem step_scanOccurrences_literal (cursor : Cursor) (data : TapeData)
    (index : Fin 3) (remaining : List OccurrenceToken)
    (occurrencesEq : data.occurrences = .literal index :: remaining) :
    machine.step (scanOccurrencesCfg cursor data) =
      some (scanOccurrencesCfg { cursor with literalIndex := index }
        { data with occurrences := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrences = _ at occurrencesEq
  subst occurrences
  cases index using Fin.cases with
  | zero =>
      simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
        cursorCfg, cfg, program, TM2.stepAux, occurrenceIsNone,
        occurrenceIsClause, occurrenceIsLiteral, cursorFromState,
        setLiteral, update_tapes_occurrences]
      rfl
  | succ index =>
      cases index using Fin.cases with
      | zero =>
          simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
            cursorCfg, cfg, program, TM2.stepAux, occurrenceIsNone,
            occurrenceIsClause, occurrenceIsLiteral, cursorFromState,
            setLiteral, update_tapes_occurrences]
          rfl
      | succ index =>
          simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
            cursorCfg, cfg, program, TM2.stepAux, occurrenceIsNone,
            occurrenceIsClause, occurrenceIsLiteral, cursorFromState,
            setLiteral, update_tapes_occurrences]
          rfl

theorem step_scanOccurrences_offset (cursor : Cursor) (data : TapeData)
    (value : Bool) (remaining : List OccurrenceToken)
    (occurrencesEq : data.occurrences = .offsetNext value :: remaining) :
    machine.step (scanOccurrencesCfg cursor data) =
      some (beginRecordCfg
        { cursor with
          anchorNext := some (cursor.anchorNext.getD value)
          currentNext := value }
        { data with occurrences := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrences = _ at occurrencesEq
  subst occurrences
  cases value <;>
    simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
      beginRecordCfg, cursorCfg, cfg, program, TM2.stepAux,
      occurrenceIsNone, occurrenceIsClause, occurrenceIsLiteral,
      occurrenceIsOffset, cursorFromState, setOffset,
      update_tapes_occurrences] <;>
    rfl

theorem step_scanOccurrences_literalEnd (cursor : Cursor) (data : TapeData)
    (remaining : List OccurrenceToken)
    (occurrencesEq : data.occurrences = .literalEnd :: remaining) :
    machine.step (scanOccurrencesCfg cursor data) =
      some (scanOccurrencesCfg cursor
        { data with occurrences := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrences = _ at occurrencesEq
  subst occurrences
  simp only [FinTM2.step, TM2.step, machine, scanOccurrencesCfg,
    cursorCfg, cfg, program, TM2.stepAux, occurrenceIsNone,
    occurrenceIsClause, occurrenceIsLiteral, occurrenceIsOffset,
    cursorFromState, clear, update_tapes_occurrences]
  rfl

theorem step_beginRecord (cursor : Cursor) (data : TapeData) :
    machine.step (beginRecordCfg cursor data) =
      some (copyCounterCfg .vertexClauses cursor
        { data with outputReverse :=
          .clauseMarker :: data.outputReverse }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, beginRecordCfg,
    copyCounterCfg, cursorCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
