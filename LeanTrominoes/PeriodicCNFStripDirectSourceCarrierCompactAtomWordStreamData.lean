/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedWordStreamData
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordData

/-! # Direct-source compact carrier atom words in global rank order -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Compact the globally ranked normalized carrier source-pair stream into
its exact constructor-tagged atom words. -/
def directSourceCarrierCompactAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  GuardedCarrierSourcePairCompactAtomWords.tokens
    (directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens
      decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
