/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrailingBitPrefixSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordAlignmentSemantics

/-! # Compacting delayed carrier constructor words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairCompactAtomWords

theorem trailingTokens_nodesAtPeriod
    (period : Nat) (nodes : List CarrierNode) :
    DelimitedBinaryWordTrailingBitPrefix.tokens
        (DelimitedBinaryWords.encode
          (GuardedCarrierSourcePairTrailingConstructor.nodeWordsAtPeriod
            period nodes)) =
      DelimitedBinaryWords.encode (wordsAtPeriod period nodes) := by
  rw [← trailingWords_nodeItemsAtPeriod]
  rw [DelimitedBinaryWordTrailingBitPrefix.tokens_encode]
  rw [prefixedWords_nodeItemsAtPeriod]

end GuardedCarrierSourcePairCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
