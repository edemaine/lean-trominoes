/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordPrefixSemantics

/-! # Fixed-suffix token semantics for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem fixedSuffix_eq_fields (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) :
    fixedSuffix literalIndex currentNext anchorNext =
      CountedUnaryFieldTokens.fields
        ([literalIndex.val, 0] ++
          SourceOccurrenceRouteEmitter.offsetFields
            currentNext anchorNext) := by
  cases currentNext <;> cases anchorNext <;>
    simp [fixedSuffix, positiveOffsetTokens, negativeOffsetTokens,
      SourceOccurrenceRouteEmitter.offsetFields,
      SourceForwardOffset.relative, SourceForwardOffset.coordinate,
      CountedUnaryFieldTokens.fields, CountedUnaryFieldTokens.field,
      PeriodicCNF.UnaryProgramTokens.atomTokens]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
