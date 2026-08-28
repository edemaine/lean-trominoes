/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTrailingConstructorCompactAtomWordSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorStreamSemantics

/-! # Exact semantics of compact atom words from guarded source pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairCompactAtomWords

/-- Guarded normalized source pairs are transformed into exactly the compact
carrier atom words, in the same stream order. -/
theorem tokens_nodesAtPeriod (period : Nat) (nodes : List CarrierNode) :
    tokens
        (DelimitedBinaryWords.encode
          (CarrierSourcePairFieldFormatter.words
            (nodes.map
              (CarrierNodeNormalizedSourceKeys.pairAtPeriod period)))) =
      DelimitedBinaryWords.encode (wordsAtPeriod period nodes) := by
  unfold tokens
  rw [GuardedCarrierSourcePairTrailingConstructor.tokens_nodesAtPeriod]
  exact trailingTokens_nodesAtPeriod period nodes

end GuardedCarrierSourcePairCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
