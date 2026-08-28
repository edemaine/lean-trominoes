/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFourWordExpansionTypedCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordBlockData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for direct-source compact carrier occurrence words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactWordBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The four occurrence words of every retained compact carrier endpoint pair
are computable in polynomial time. -/
noncomputable def directSourceCarrierCompactAtomWordBlockComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token id
      DelimitedBinaryWords.finEncoding.encode
      (directSourceCarrierCompactAtomWordBlock decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceCarrierRetainedCompactAtomWordPairsComputableInPolyTime
      decider)
    DelimitedBinaryWordPairFourWordExpansion.expandedInputComputableInPolyTime
  change @TM2ComputableInPolyTime
    (List encoding.Γ) DelimitedBinaryWords.Input
    encoding.Γ DelimitedBinaryWords.Token id
    DelimitedBinaryWords.finEncoding.encode
    (fun symbols =>
      DelimitedBinaryWordPairFourWordExpansion.expandedInput
        (directSourceCarrierRetainedCompactAtomWordPairs decider symbols))
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
