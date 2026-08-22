/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordOutputData

/-! # Exact one-record output semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem countedField_reverse (number : Nat) :
    (CountedUnaryFieldTokens.field number).reverse =
      .atomEnd :: List.replicate number (.atomUnit : OutputToken) := by
  simp [CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens]

theorem afterFinishedRecordData_eq (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) :
    afterFinishedRecordData
        (afterRecordCounters (beginRecordData data))
        targetCount remainingTargets literalIndex currentNext anchorNext =
      { data with
        scratch := []
        targets := remainingTargets
        edgeIndex := () :: data.edgeIndex
        outputReverse :=
          (emittedRecordTokens data targetCount literalIndex
            currentNext anchorNext).reverse ++ data.outputReverse } := by
  rw [afterRecordCounters_beginRecordData_eq]
  simp only [afterFinishedRecordData, afterTargetData,
    emittedRecordTokens, recordCounterPrefix, List.reverse_append,
    List.reverse_reverse, countedField_reverse, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
