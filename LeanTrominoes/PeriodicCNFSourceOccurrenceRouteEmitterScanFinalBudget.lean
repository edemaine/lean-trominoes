/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanBudget

/-! # Final occurrence-scan budget -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

theorem scanSize_final_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    scanSize base
        (scan base.clauseCount.length base.literalCount.length state tokens) [] ≤
      scanSize base state tokens := by
  induction tokens generalizing state with
  | nil =>
      exact Nat.le_refl _
  | cons token tokens induction =>
      cases token with
      | clause arity =>
          exact (induction state.readClause).trans
            (scanSize_readClause_le base state arity tokens)
      | literal index =>
          exact (induction (state.readLiteral index)).trans
            (scanSize_readLiteral_le base state index tokens)
      | offsetNext value =>
          exact (induction
            (state.readOffset base.clauseCount.length
              base.literalCount.length value)).trans
            (scanSize_readOffset_le base state value tokens)
      | literalEnd =>
          exact (induction state).trans
            (scanSize_literalEnd_le base state tokens)

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
