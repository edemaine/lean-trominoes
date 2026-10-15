/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Crossover.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Crossover.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordTokenCompiler
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Named physical direct-source crossover token compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
