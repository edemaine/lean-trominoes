/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableTerminalChoices
import LeanTrominoes.RetainedAngularFanNormalizedClauseRouteTailRecordStreamSemantics

/-! # Normalized semantics of routed-variable record queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedVariableNormalizedQueryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedVariableNormalizedQueryVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalRoutedVariableRecordQueryStream_eq_normalizedSemantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordStream
        (((directSourceFinalRoutedVariableClauses decider symbols).zipIdx
            (directSourceFinalRoutedVariableStart decider symbols)).map
          fun taggedClause =>
            retainedFinalDirectClauseRouteTailRecordQuery
              (directSourceFormula decider symbols)
              taggedClause.2 ⟨(0, 0), taggedClause.1⟩) =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        (directSourceFormula decider symbols)
        (directSourceFinalRoutedVariableStart decider symbols)
        (directSourceFinalRoutedVariableClauses decider symbols) := by
  apply @retainedFinalNormalizedClauseRouteTailRecordStream_eq
    Variable directSourceVariableDecidableEq
    (directSourceFormula decider symbols)
    (sourceFormula_isLocal
      (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_widthAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_occurrencesAtMostThree_canonicalBEq
      (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_clausesNonempty
      (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (directSourceFinalRoutedVariableStart decider symbols)
    (directSourceFinalRoutedVariableClauses decider symbols)
  · intro taggedClause taggedMember
    simpa only [directSourceFinalRoutedVariableTaggedClauses,
      directSourceFinalRoutedVariableTaggedSourceClauses] using
      directSourceFinalRoutedVariableClauses_indexedMember
        decider symbols taggedClause taggedMember
  · intro taggedClause taggedMember
    exact directSourceFinalRoutedVariableClauses_nonempty
      decider symbols taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  · intro taggedClause taggedMember
    exact directSourceFinalRoutedVariableClauses_widthAtMostThree
      decider symbols taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  · have routeChoices : FinalIndexedClauseRouteChoices
        (directSourceFormula decider symbols)
        (directSourceFinalRoutedVariableStart decider symbols)
        (directSourceFinalRoutedVariableClauses decider symbols) := by
      rw [directSourceFormula_eq_finalNormalized]
      exact directSourceFinalRoutedVariableRouteChoices decider symbols
    exact routeChoices.choices

end LeanTrominoes.PeriodicCNFStripReduction

end
