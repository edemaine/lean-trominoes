/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Source-record source-index field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def sourceSourceCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .sourceSourceLiteral tag data)
      (some (scanTargetCfg tag (afterSourceSourceCounters data)))
      (sourceSourceCountersTime data) := by
  have literal := counter_evalsInTime .sourceSourceLiteral tag data
    data.literalCount rfl scratchEq
  have literal' : EvalsToInTime machine.step
      (copyCounterCfg .sourceSourceLiteral tag data)
      (some (copyCounterCfg .sourceSourceClause tag
        (afterSourceSourceLiteralCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterSourceSourceLiteralCounter] using literal
  have clauses := counter_evalsInTime .sourceSourceClause tag
    (afterSourceSourceLiteralCounter data) data.clauseCount rfl rfl
  have clauses' : EvalsToInTime machine.step
      (copyCounterCfg .sourceSourceClause tag
        (afterSourceSourceLiteralCounter data))
      (some (copyCounterCfg .sourceSourceIndex tag
        (afterSourceSourceClauseCounter data)))
      (counterTime data.clauseCount) := by
    simpa only [afterCounterCfg,
      afterSourceSourceClauseCounter] using clauses
  have index := counter_evalsInTime .sourceSourceIndex tag
    (afterSourceSourceClauseCounter data) data.linkIndex rfl rfl
  have index' : EvalsToInTime machine.step
      (copyCounterCfg .sourceSourceIndex tag
        (afterSourceSourceClauseCounter data))
      (some (scanTargetCfg tag (afterSourceSourceCounters data)))
      (counterTime data.linkIndex) := by
    simpa only [afterCounterCfg, afterSourceSourceCounters,
      closeOutputField, afterSourceSourceClauseCounter] using index
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.clauseCount)
    _ _ _ literal' clauses'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.clauseCount + counterTime data.literalCount)
    (counterTime data.linkIndex) _ _ _ firstTwo index'
  simpa only [sourceSourceCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
