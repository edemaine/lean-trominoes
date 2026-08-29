/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFigureNinePolarityRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.RetainedAngularFanNormalizedClauseRouteTailRecordSemantics

/-! # Five-family semantics of direct copied Figure 9 records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCopiedRecordFamilySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCopiedRecordFamilySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The canonical copied record word follows the exact five-family clause
order and carries each family's original global starting index. -/
theorem directFigureNineCopiedRouteTailRecordTokens_eq_fiveFamilies
    (symbols : List encoding.Γ) :
    directFigureNineCopiedRouteTailRecordTokens decider symbols =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols) 0
          (directSourceFinalCrossoverClauses decider symbols) ++
        retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
            (directSourceFormula decider symbols)
            (directSourceFinalCarrierStart decider symbols)
            (directSourceFinalCarrierClauses decider symbols) ++
          retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
              (directSourceFormula decider symbols)
              (directSourceFinalBendStart decider symbols)
              (directSourceFinalBendClauses decider symbols) ++
            retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
                (directSourceFormula decider symbols)
                (directSourceFinalRoutedClauseStart decider symbols)
                (directSourceFinalRoutedClauseClauses decider symbols) ++
              retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
                (directSourceFormula decider symbols)
                (directSourceFinalRoutedVariableStart decider symbols)
                (directSourceFinalRoutedVariableClauses decider symbols) := by
  unfold directFigureNineCopiedRouteTailRecordTokens
  rw [copiedRecordTokens_eq_normalizedClauseSemantic]
  rw [directSource_deduplicatedClauses_eq_fiveFamilies,
    directSourceFinalFiveFamilyClauses_eq_named]
  simp only [retainedFinalNormalizedClauseSemanticRouteTailRecordTokens_append,
    List.length_append, Nat.zero_add]
  simp [directSourceFinalCarrierStart, directSourceFinalBendStart,
    directSourceFinalRoutedClauseStart,
    directSourceFinalRoutedVariableStart, Nat.add_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
