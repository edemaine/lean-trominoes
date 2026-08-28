/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceTargetAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceTargetAtomWordTokenCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct-source target-vertex atom-word compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTargetAtomWordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct symbols compile to one exact indexed source-atom word per route
descriptor in polynomial time. -/
noncomputable def directSourceTargetAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceTargetAtomWords decider) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceTargetAtomWordTokensComputableInPolyTime decider)
    fun symbols => by
      simpa only [id_eq, DelimitedBinaryWords.finEncoding] using
        directSourceTargetAtomWordTokens_eq_encode decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
