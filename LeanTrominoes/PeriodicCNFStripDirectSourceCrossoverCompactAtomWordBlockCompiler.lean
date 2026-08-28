/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordFinalTokenSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordTokenAliasCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for the final direct crossover compact atom-word block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverCompactBlockCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverCompactBlockCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The exact final crossover compact word block is polynomial-time
computable from direct source symbols. -/
noncomputable def
    directSourceFinalCompactCrossoverAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactCrossoverAtomWords decider) :=
  TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
    (directSourceCrossoverCompactAtomWordTokensComputableInPolyTime decider)
    fun symbols => by
      rw [directSourceCrossoverCompactAtomWordTokens_eq_finalBlock]
      rw [← directSourceFinalCompactCrossoverAtomWords_eq_block]
      exact (DelimitedBinaryWords.finEncoding_encode _).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
