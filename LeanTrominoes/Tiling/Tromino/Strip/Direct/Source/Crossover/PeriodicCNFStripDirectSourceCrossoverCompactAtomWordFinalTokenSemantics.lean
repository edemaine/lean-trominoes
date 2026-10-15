/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Crossover.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordBlockSemantics

/-! # Exact physical direct-source crossover compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directCrossoverFinalTokenSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The polynomial physical token stream encodes exactly the official final
crossover-family compact atom-word block. -/
theorem directSourceCrossoverCompactAtomWordTokens_eq_finalBlock
    (symbols : List encoding.Γ) :
    directSourceCrossoverCompactAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        ⟨directSourceFinalCompactCrossoverAtomWordBlock decider symbols⟩ := by
  rw [directSourceCrossoverCompactAtomWordTokens_eq_encode]
  rw [directSourceCanonicalCrossoverCompactAtomWords_eq_final]
  rw [directSourceFinalCompactCrossoverAtomWords_eq_block]

end PeriodicCNFStripReduction
end LeanTrominoes

end
