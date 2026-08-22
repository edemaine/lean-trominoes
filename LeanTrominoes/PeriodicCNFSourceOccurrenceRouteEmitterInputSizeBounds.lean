/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInitialExecutionData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanBudget

/-! # Encoded-input size bounds for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

@[simp] theorem encode_length (input : SourceOccurrenceRouteEmitter.Input) :
    (SourceOccurrenceRouteEmitter.encode input).length =
      input.occurrences.length +
        ((UnaryFieldEncoderMachine.unaryFields input.targets).length + 1) := by
  simp [SourceOccurrenceRouteEmitter.encode,
    SeparatedProductEncoding.encode]

theorem one_le_encode_length (input : SourceOccurrenceRouteEmitter.Input) :
    1 ≤ (SourceOccurrenceRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem occurrences_length_le_encode_length
    (input : SourceOccurrenceRouteEmitter.Input) :
    input.occurrences.length ≤
      (SourceOccurrenceRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem occurrences_length_add_one_le_encode_length
    (input : SourceOccurrenceRouteEmitter.Input) :
    input.occurrences.length + 1 ≤
      (SourceOccurrenceRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem unaryTargets_length_le_encode_length
    (input : SourceOccurrenceRouteEmitter.Input) :
    (UnaryFieldEncoderMachine.unaryFields input.targets).length ≤
      (SourceOccurrenceRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem initial_scanSize_le (input : SourceOccurrenceRouteEmitter.Input) :
    scanSize (initialBase input.occurrences)
        (initialScanState input.targets) input.occurrences ≤
      3 * (SourceOccurrenceRouteEmitter.encode input).length := by
  have clauseLe := UnaryPolynomialPaddingMachine.selectedCount_le_length
    SourceOccurrenceRouteTokens.isClause input.occurrences
  have literalLe := UnaryPolynomialPaddingMachine.selectedCount_le_length
    SourceOccurrenceRouteTokens.isLiteral input.occurrences
  rw [encode_length]
  simp only [scanSize, initialBase_clauseCount_length,
    initialBase_literalCount_length, initialScanState]
  omega

theorem parseTime_eq_four_encode_length
    (input : SourceOccurrenceRouteEmitter.Input) :
    parseTime input.occurrences
        (UnaryFieldEncoderMachine.unaryFields input.targets) =
      4 * (SourceOccurrenceRouteEmitter.encode input).length := by
  rw [encode_length]
  simp only [parseTime]
  omega

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
