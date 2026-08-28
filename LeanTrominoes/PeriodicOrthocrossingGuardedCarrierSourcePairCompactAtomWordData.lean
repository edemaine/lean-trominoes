/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrailingBitPrefixData
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorData

/-! # Exact compact atom words from guarded carrier source pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairCompactAtomWords

/-- Classify each source pair with a trailing constructor bit, then move that
bit behind the fixed leading `false`. -/
def tokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordTrailingBitPrefix.tokens
    (GuardedCarrierSourcePairTrailingConstructor.tokens source)

def wordsAtPeriod (period : Nat) (nodes : List CarrierNode) :
    DelimitedBinaryWords.Input :=
  ⟨nodes.map (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod period)⟩

end GuardedCarrierSourcePairCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
