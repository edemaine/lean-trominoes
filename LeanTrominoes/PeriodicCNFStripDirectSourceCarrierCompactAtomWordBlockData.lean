/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFourWordExpansionData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairData

/-! # Direct-source compact carrier occurrence words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Expand each retained compact carrier endpoint pair into its four word
occurrences, in retained-pair order. -/
def directSourceCarrierCompactAtomWordBlock
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWordPairFourWordExpansion.expandedInput
    (directSourceCarrierRetainedCompactAtomWordPairs decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
