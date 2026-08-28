/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairMaskCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairProductCompiler

/-! # Raw retained carrier-pair filtering over nonempty alphabets -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierPairFilterNonemptyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Positional filtering is polynomial-time when the source alphabet has a
symbol available to the generic input-fork machine. -/
noncomputable def
    directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTimeOfInhabited
    [Inhabited encoding.Γ] :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.encode
      (fun symbols =>
        ⟨DelimitedBinaryWordPairBooleanFilter.selectedPairs
          (directSourceCarrierRetainedPairMask decider symbols)
          (directSourceCarrierCompactAtomWordPairs decider symbols).pairs⟩) :=
  DelimitedBinaryWordPairBooleanFilter.filteredPairsComputableInPolyTime
    id
    (directSourceCarrierRetainedPairMask decider)
    (directSourceCarrierCompactAtomWordPairs decider)
    (directSourceCarrierRetainedPairMaskComputableInPolyTime decider)
    (directSourceCarrierCompactAtomWordPairsComputableInPolyTime decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
