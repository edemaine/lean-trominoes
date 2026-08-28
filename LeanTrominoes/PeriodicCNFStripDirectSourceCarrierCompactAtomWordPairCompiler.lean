/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairFilterCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for retained direct-source compact carrier word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactPairCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The retained compact endpoint pairs in global key-major link order are
computable in polynomial time. -/
noncomputable def
    directSourceCarrierRetainedCompactAtomWordPairsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWordPairs.Input
      encoding.Γ DelimitedBinaryWordPairs.Token id
      DelimitedBinaryWordPairs.finEncoding.encode
      (directSourceCarrierRetainedCompactAtomWordPairs decider) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceCarrierSelectedCompactAtomWordPairsComputableInPolyTime
      decider)
    fun symbols => by
      rw [directSourceCarrierRetainedCompactAtomWordPairs_eq_selected]
      exact (DelimitedBinaryWordPairs.finEncoding_encode _).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
