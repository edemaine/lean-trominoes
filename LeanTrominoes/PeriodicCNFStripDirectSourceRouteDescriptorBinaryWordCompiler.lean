/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordTokenCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Semantic direct compiler for binary route-descriptor words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorBinaryWordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct source symbols compile to the exact semantic list of binary
descriptor words in polynomial time. -/
noncomputable def directSourceRouteDescriptorBinaryWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (fun symbols =>
        directSourceRouteDescriptorBinaryWords decider symbols) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceRouteDescriptorBinaryWordTokensComputableInPolyTime decider)
    fun symbols => by
      simpa only [id_eq, DelimitedBinaryWords.finEncoding] using
        directSourceRouteDescriptorBinaryWordTokens_eq_encode decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
