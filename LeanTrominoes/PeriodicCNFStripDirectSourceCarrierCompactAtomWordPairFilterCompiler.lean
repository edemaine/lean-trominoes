/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairFilterEmptyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairFilterNonemptySemanticCompiler

/-! # Raw filter compiler for retained direct carrier-word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactPairFilterStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Positional filtering of the direct compact carrier-word square is
computable in polynomial time for every finite source alphabet. -/
noncomputable def
    directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.encode
      (directSourceCarrierSelectedCompactAtomWordPairs decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
      letI : Inhabited encoding.Γ :=
        ⟨Classical.choice nonemptyAlphabet⟩
      exact
        directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTimeOfInhabitedSemantic
          decider
    else by
      letI : IsEmpty encoding.Γ :=
        ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
      exact
        directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTimeOfEmpty
          decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
