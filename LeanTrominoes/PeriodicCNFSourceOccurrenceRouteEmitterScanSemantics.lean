/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # Pure occurrence-scan semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

theorem semanticCursor_readClause (state : ScanState) :
    state.readClause.semanticCursor =
      { state.semanticCursor with
        nextClauseIndex := state.semanticCursor.nextClauseIndex + 1
        clauseIndex := state.semanticCursor.nextClauseIndex
        anchorNext := none } := by
  cases state.cursor.seenClause <;>
    simp [ScanState.readClause, ScanState.semanticCursor]

@[simp] theorem semanticCursor_readLiteral (state : ScanState)
    (index : Fin 3) :
    (state.readLiteral index).semanticCursor =
      { state.semanticCursor with literalIndex := index } := by
  rfl

@[simp] theorem semanticCursor_target (state : ScanState) :
    state.semanticCursor.target = state.targets.head?.getD 0 := by
  rfl

@[simp] theorem semanticCursor_clauseIndex (state : ScanState) :
    state.semanticCursor.clauseIndex = state.clauseIndex := by
  rfl

@[simp] theorem semanticCursor_edgeIndex (state : ScanState) :
    state.semanticCursor.edgeIndex = state.edgeIndex := by
  rfl

@[simp] theorem semanticCursor_literalIndex (state : ScanState) :
    state.semanticCursor.literalIndex = state.cursor.literalIndex := by
  rfl

@[simp] theorem semanticCursor_anchorNext (state : ScanState) :
    state.semanticCursor.anchorNext = state.cursor.anchorNext := by
  rfl

@[simp] theorem semanticCursor_remainingTargets (state : ScanState) :
    state.semanticCursor.remainingTargets = state.targets.drop 1 := by
  rfl

theorem semanticCursor_readOffset (clauseCount literalCount : Nat)
    (state : ScanState) (value : Bool) :
    (state.readOffset clauseCount literalCount value).semanticCursor =
      { state.semanticCursor with
        edgeIndex := state.semanticCursor.edgeIndex + 1
        anchorNext := some (state.cursor.anchorNext.getD value)
        targets := state.semanticCursor.remainingTargets } := by
  rfl

theorem scan_emitted (clauseCount literalCount : Nat)
    (state : ScanState) (tokens : List Token) :
    (scan clauseCount literalCount state tokens).emitted =
      state.emitted ++
        SourceOccurrenceRouteEmitter.emitAux clauseCount literalCount
          state.semanticCursor tokens := by
  induction tokens generalizing state with
  | nil =>
      simp only [scan, SourceOccurrenceRouteEmitter.emitAux,
        List.append_nil]
  | cons token tokens induction =>
      cases token with
      | clause arity =>
          simp only [scan, SourceOccurrenceRouteEmitter.emitAux]
          rw [induction, semanticCursor_readClause]
          rfl
      | literal index =>
          simp only [scan, SourceOccurrenceRouteEmitter.emitAux]
          rw [induction, semanticCursor_readLiteral]
          rfl
      | offsetNext value =>
          simp only [scan, SourceOccurrenceRouteEmitter.emitAux]
          rw [induction, semanticCursor_readOffset]
          simp only [ScanState.readOffset, semanticCursor_clauseIndex,
            semanticCursor_edgeIndex, semanticCursor_literalIndex,
            semanticCursor_anchorNext, semanticCursor_target,
            semanticCursor_remainingTargets, List.append_assoc]
      | literalEnd =>
          simp only [scan, SourceOccurrenceRouteEmitter.emitAux]
          rw [induction]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
