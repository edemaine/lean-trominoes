/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordCounterData

/-! # Source-vertex field execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def sourceCounters_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .sourceLiterals cursor data)
      (some (scanTargetCfg cursor (afterSourceCounters data)))
      (sourceCountersTime data) := by
  have literals := counter_evalsInTime .sourceLiterals cursor data
    data.literalCount rfl scratchEq
  have literals' : EvalsToInTime machine.step
      (copyCounterCfg .sourceLiterals cursor data)
      (some (copyCounterCfg .sourceClauses cursor
        (afterSourceLiteralCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterSourceLiteralCounter] using literals
  have clauses := counter_evalsInTime .sourceClauses cursor
    (afterSourceLiteralCounter data) data.clauseIndex rfl rfl
  have clauses' : EvalsToInTime machine.step
      (copyCounterCfg .sourceClauses cursor
        (afterSourceLiteralCounter data))
      (some (scanTargetCfg cursor (afterSourceCounters data)))
      (counterTime data.clauseIndex) := by
    simpa only [afterCounterCfg, afterSourceCounters, closeOutputField,
      afterSourceLiteralCounter] using clauses
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.clauseIndex)
    (copyCounterCfg .sourceLiterals cursor data)
    (copyCounterCfg .sourceClauses cursor
      (afterSourceLiteralCounter data))
    (some (scanTargetCfg cursor (afterSourceCounters data)))
    literals' clauses'
  simpa only [sourceCountersTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
