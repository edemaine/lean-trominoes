/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOccurrenceSteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # Clause-header scan-state step -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem step_scanData_clause (base : TapeData) (state : ScanState)
    (arity : Fin 4) (tokens : List SourceOccurrenceRouteTokens.Token) :
    machine.step (scanOccurrencesCfg state.cursor
        (scanData base state (.clause arity :: tokens))) =
      some (scanOccurrencesCfg state.readClause.cursor
        (scanData base state.readClause tokens)) := by
  cases seen : state.cursor.seenClause with
  | false =>
      have step := step_scanOccurrences_firstClause state.cursor
        (scanData base state (.clause arity :: tokens)) arity tokens
        seen rfl
      simpa [scanData, ScanState.readClause, seen]
        using step
  | true =>
      have step := step_scanOccurrences_nextClause state.cursor
        (scanData base state (.clause arity :: tokens)) arity tokens
        seen rfl
      simpa [scanData, ScanState.readClause, seen,
        List.replicate_succ] using step

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
