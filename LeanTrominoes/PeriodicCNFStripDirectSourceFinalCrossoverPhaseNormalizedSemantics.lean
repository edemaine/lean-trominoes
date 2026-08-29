/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverPhaseRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverNormalizedRecordQuerySemantics

/-! # Normalized-clause semantics of the crossover record phase -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverNormalizedSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
