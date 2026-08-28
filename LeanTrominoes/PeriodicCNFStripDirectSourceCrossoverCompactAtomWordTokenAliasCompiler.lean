/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordData
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordTokenCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Named physical direct-source crossover token compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverTokenAliasCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverTokenAliasCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The raw compiler's explicit output lambda is definitionally the named
physical token function. -/
noncomputable def
    directSourceCrossoverCompactAtomWordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token id id
      (directSourceCrossoverCompactAtomWordTokens decider) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := directSourceCrossoverCompactAtomWordTokens decider)
    (directSourceCrossoverCompactAtomWordRawTokensComputableInPolyTime
      decider)
    (fun _ => rfl)

end PeriodicCNFStripReduction
end LeanTrominoes

end
