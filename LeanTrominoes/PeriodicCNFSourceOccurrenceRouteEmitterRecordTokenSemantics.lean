/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordSuffixSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordOutputSemantics

/-! # Complete one-record token semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem emittedRecordTokens_eq_routeTokens (data : TapeData)
    (targetCount : Nat) (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) :
    emittedRecordTokens data targetCount literalIndex currentNext anchorNext =
      SourceOccurrenceRouteEmitter.routeTokens
        data.clauseCount.length data.literalCount.length
        data.clauseIndex.length data.edgeIndex.length literalIndex
        targetCount currentNext anchorNext := by
  simp only [emittedRecordTokens, recordCounterPrefix_eq,
    fixedSuffix_eq_fields, SourceOccurrenceRouteEmitter.routeTokens,
    SourceOccurrenceRouteEmitter.routeFields,
    CountedUnaryFieldTokens.countedFieldBlock,
    CountedUnaryFieldTokens.fields, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.append_nil, List.append_assoc]

theorem afterFinishedRecordData_eq_routeTokens (data : TapeData)
    (targetCount : Nat) (remainingTargets : List UnarySymbol)
    (literalIndex : Fin 3) (currentNext anchorNext : Bool) :
    afterFinishedRecordData
        (afterRecordCounters (beginRecordData data))
        targetCount remainingTargets literalIndex currentNext anchorNext =
      { data with
        scratch := []
        targets := remainingTargets
        edgeIndex := () :: data.edgeIndex
        outputReverse :=
          (SourceOccurrenceRouteEmitter.routeTokens
            data.clauseCount.length data.literalCount.length
            data.clauseIndex.length data.edgeIndex.length literalIndex
            targetCount currentNext anchorNext).reverse ++
              data.outputReverse } := by
  rw [afterFinishedRecordData_eq,
    emittedRecordTokens_eq_routeTokens]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
