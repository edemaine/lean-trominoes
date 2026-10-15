/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverPhaseRouteTailRecordSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverNormalizedRecordQuerySemantics

/-! # Normalized-clause semantics of the crossover record phase -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directCrossoverNormalizedSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled crossover phase is exactly the normalized semantic record
block at global clause index zero. -/
theorem directSourceFinalCrossoverRouteTailRecordTokens_eq_normalizedSemantic
    (symbols : List encoding.Γ) :
    directSourceFinalCrossoverRouteTailRecordTokens decider symbols =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        (directSourceFormula decider symbols) 0
        (directSourceFinalCrossoverClauses decider symbols) := by
  rw [directSourceFinalCrossoverRouteTailRecordTokens_eq_semantic]
  exact directSourceFinalCrossoverRecordQueryStream_eq_normalizedSemantic
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
