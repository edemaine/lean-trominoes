/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsDecode
import LeanTrominoes.PeriodicCNFStripDirectSourceTargetAtomWordTokenData

/-! # Semantic target-vertex atom words for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTargetAtomWordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Decode the physical target-index word stream.  The fallback is unreachable
for the canonical direct-source stream and keeps this semantic interface total. -/
def directSourceTargetAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWords.decodeOrEmpty
    (directSourceTargetAtomWordTokens decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
