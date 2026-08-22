/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInitialScanData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterParseToScanExecution

/-! # Initial full-execution data for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def initialBase (occurrences : List OccurrenceToken) : TapeData :=
  ⟨[], [], [], [], [],
    countTape SourceOccurrenceRouteTokens.isClause occurrences,
    countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
    [], [], [], [], []⟩

@[simp] theorem initialBase_clauseCount_length
    (occurrences : List OccurrenceToken) :
    (initialBase occurrences).clauseCount.length =
      UnaryPolynomialPaddingMachine.selectedCount
        SourceOccurrenceRouteTokens.isClause occurrences := by
  simp [initialBase, countTape]

@[simp] theorem initialBase_literalCount_length
    (occurrences : List OccurrenceToken) :
    (initialBase occurrences).literalCount.length =
      UnaryPolynomialPaddingMachine.selectedCount
        SourceOccurrenceRouteTokens.isLiteral occurrences := by
  simp [initialBase, countTape]

@[simp] theorem initial_scanData (occurrences : List OccurrenceToken)
    (targets : List Nat) :
    scanData (initialBase occurrences) (initialScanState targets) occurrences =
      ⟨[], [], occurrences, [],
        UnaryFieldEncoderMachine.unaryFields targets,
        countTape SourceOccurrenceRouteTokens.isClause occurrences,
        countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
        [], [], [], [], []⟩ := by
  rfl

theorem initial_scan_emitted (input : SourceOccurrenceRouteEmitter.Input) :
    (scan
      (initialBase input.occurrences).clauseCount.length
      (initialBase input.occurrences).literalCount.length
      (initialScanState input.targets) input.occurrences).emitted =
      SourceOccurrenceRouteEmitter.emit input := by
  simp only [initialBase_clauseCount_length,
    initialBase_literalCount_length, SourceOccurrenceRouteEmitter.emit]
  exact scan_initial_emitted _ _ input.targets input.occurrences

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
