/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseNormalizedRecordQuerySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedPhaseRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableNormalizedRecordQuerySemantics

/-! # Normalized-clause semantics of the routed record phase -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedNormalizedSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedNormalizedSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled routed phase is exactly the normalized routed-clause block
followed by the normalized routed-variable block. -/
theorem directSourceFinalRoutedRouteTailRecordTokens_eq_normalizedSemantic
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedRouteTailRecordTokens decider symbols =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalRoutedClauseStart decider symbols)
          (directSourceFinalRoutedClauseClauses decider symbols) ++
        retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalRoutedVariableStart decider symbols)
          (directSourceFinalRoutedVariableClauses decider symbols) := by
  rw [directSourceFinalRoutedRouteTailRecordTokens_eq_semantic,
    directSourceFinalRoutedClauseRecordQueryStream_eq_normalizedSemantic,
    directSourceFinalRoutedVariableRecordQueryStream_eq_normalizedSemantic]

end LeanTrominoes.PeriodicCNFStripReduction

end
