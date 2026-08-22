/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenData
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.UnaryFieldEncoderMachine
import LeanTrominoes.UnaryPolynomialPaddingMachine

/-! # Input records for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

abbrev InputSymbol := SeparatedProductEncoding.Token
  SourceOccurrenceRouteTokens.Token UnaryFieldEncoderMachine.Symbol

/-- A finite occurrence stream paired with one unary target index per
occurrence. -/
structure Input where
  occurrences : List SourceOccurrenceRouteTokens.Token
  targets : List Nat
  valid : targets.length =
    UnaryPolynomialPaddingMachine.selectedCount
      SourceOccurrenceRouteTokens.isLiteral occurrences

/-- Physical separated encoding consumed by the route emitter. -/
def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode id
    UnaryFieldEncoderMachine.unaryFields
    (input.occurrences, input.targets)

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
