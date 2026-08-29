/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseTerminalChoices
import LeanTrominoes.RetainedAngularFanNormalizedClauseRouteTailRecordStreamSemantics

/-! # Normalized semantics of routed-clause record queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedClauseNormalizedQueryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedClauseNormalizedQueryVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalRoutedClauseRecordQueryStream_eq_normalizedSemantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordStream
        (((directSourceFinalRoutedClauseClauses decider symbols).zipIdx
            (directSourceFinalRoutedClauseStart decider symbols)).map
          fun taggedClause =>
            retainedFinalDirectClauseRouteTailRecordQuery
              (directSourceFormula decider symbols)
              taggedClause.2 ⟨(0, 0), taggedClause.1⟩) =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        (directSourceFormula decider symbols)
        (directSourceFinalRoutedClauseStart decider symbols)
        (directSourceFinalRoutedClauseClauses decider symbols) := by
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
    (directSourceFinalRoutedClauseStart decider symbols)
    (directSourceFinalRoutedClauseClauses decider symbols)
  · intro taggedClause taggedMember
    simpa only [directSourceFinalRoutedClauseTaggedClauses,
      directSourceFinalRoutedClauseTaggedSourceClauses] using
      directSourceFinalRoutedClauseClauses_indexedMember
        decider symbols taggedClause taggedMember
  · intro taggedClause taggedMember
    exact directSourceFinalRoutedClauseClauses_nonempty
      decider symbols taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  · intro taggedClause taggedMember
    exact directSourceFinalRoutedClauseClauses_widthAtMostThree
      decider symbols taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  · have routeChoices : FinalIndexedClauseRouteChoices
        (directSourceFormula decider symbols)
        (directSourceFinalRoutedClauseStart decider symbols)
        (directSourceFinalRoutedClauseClauses decider symbols) := by
      rw [directSourceFormula_eq_finalNormalized]
      exact directSourceFinalRoutedClauseRouteChoices decider symbols
    exact routeChoices.choices

end LeanTrominoes.PeriodicCNFStripReduction

end
