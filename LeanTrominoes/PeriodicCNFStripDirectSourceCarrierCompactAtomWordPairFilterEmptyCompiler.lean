/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairFilterEmptyConstantCompiler
import LeanTrominoes.TM2PolyTimeFunctionTransport

/-! # Raw retained carrier-pair filtering over an empty alphabet -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierPairFilterEmptyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- If the source alphabet is empty, its symbol-list domain contains only
the empty word, so the retained output is a fixed finite constant. -/
noncomputable def
    directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTimeOfEmpty
    [IsEmpty encoding.Γ] :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.encode
      (directSourceCarrierSelectedCompactAtomWordPairs decider) := by
  exact TM2PolyTimeFunctionTransport.of_output_eq
    (directSourceCarrierSelectedCompactAtomWordPairsAtNilComputableInPolyTime
      decider)
    fun symbols =>
      (directSourceCarrierSelectedCompactAtomWordPairs_eq_nil_of_isEmpty
        decider symbols).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
