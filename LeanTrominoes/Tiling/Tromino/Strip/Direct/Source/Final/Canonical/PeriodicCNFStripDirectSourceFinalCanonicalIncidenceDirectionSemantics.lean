/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Canonical.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceDirectionCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Clause.PeriodicCNFStripDirectSourceFinalClauseIncidenceDirectionSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Grouped.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionSemantics

/-! # Semantics of the direct final canonical incidence stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- The final stream exposes the exact variable-prefix/sparse-suffix join,
followed by the exact finite clause-core block family. -/
theorem directSourceFinalCanonicalIncidenceDirectionTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.joined
        (directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
          decider symbols)
        (VariableIncidenceSparseSuffixToken.output
          (directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
            decider symbols)) ++
      FiniteAlphabetDelimitedBlockJoin.blocks
        ((directSourceFinalClauseIncidenceQueries decider symbols).map
          HorizontalFiniteIncidenceDirectionQuery.directions) := by
  unfold directSourceFinalCanonicalIncidenceDirectionTokens
  rw [directSourceFinalGroupedVariableIncidenceDirectionTokens_eq_joined,
    directSourceFinalClauseIncidenceDirectionTokens_eq_blocks]

end LeanTrominoes.PeriodicCNFStripReduction

end
