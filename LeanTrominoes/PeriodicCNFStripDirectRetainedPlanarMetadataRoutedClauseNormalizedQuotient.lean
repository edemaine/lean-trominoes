/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseBaseNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData

/-! # Direct normalized routed-clause quotient -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedClauseQuotientStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedClauseQuotientVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- For every direct source, stable normalization retains exactly one routed
source clause per source-clause index. -/
theorem directRetainedPlanarMetadataRoutedClauseNormalized_dedup_eq_base
    (symbols : List encoding.Γ) :
    (routedClauseMetadataNormalizedClauses
      (directSourceFormula decider symbols)).dedup =
        baseRoutedClauseNormalizedClauses
          (directSourceFormula decider symbols) := by
  apply routedClauseMetadataNormalizedClauses_dedup_eq_base
  · exact PeriodicCNF.incidenceGraph_isWellFormed _
  · unfold directSourceFormula
    exact sourceFormula_clausesNonempty _

end LeanTrominoes.PeriodicCNFStripReduction

end
