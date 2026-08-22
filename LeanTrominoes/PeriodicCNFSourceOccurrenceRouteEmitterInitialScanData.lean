/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanSemantics

/-! # Initial occurrence-scan state -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def initialScanState (targets : List Nat) : ScanState where
  cursor := initialCursor
  clauseIndex := 0
  edgeIndex := 0
  targets := targets
  emitted := []

@[simp] theorem initialScanState_semanticCursor (targets : List Nat) :
    (initialScanState targets).semanticCursor =
      SourceOccurrenceRouteEmitter.initialCursor targets := by
  rfl

theorem scan_initial_emitted (clauseCount literalCount : Nat)
    (targets : List Nat) (tokens : List SourceOccurrenceRouteTokens.Token) :
    (scan clauseCount literalCount (initialScanState targets) tokens).emitted =
      SourceOccurrenceRouteEmitter.emitAux clauseCount literalCount
        (SourceOccurrenceRouteEmitter.initialCursor targets) tokens := by
  rw [scan_emitted, initialScanState_semanticCursor]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
