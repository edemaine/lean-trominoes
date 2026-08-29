/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverTerminalChoices
import LeanTrominoes.RetainedAngularFanNormalizedClauseRouteTailRecordStreamSemantics

/-! # Normalized semantics of crossover record queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverNormalizedQueryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverNormalizedQueryVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The globally indexed crossover record-query stream evaluates to its
normalized semantic record block. -/
theorem directSourceFinalCrossoverRecordQueryStream_eq_normalizedSemantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordStream
        (((directSourceFinalCrossoverClauses decider symbols).zipIdx 0).map
          fun taggedClause =>
            retainedFinalDirectClauseRouteTailRecordQuery
              (directSourceFormula decider symbols)
              taggedClause.2 ⟨(0, 0), taggedClause.1⟩) =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        (directSourceFormula decider symbols) 0
        (directSourceFinalCrossoverClauses decider symbols) := by
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
    0
    (directSourceFinalCrossoverClauses decider symbols)
  · intro taggedClause taggedMember
    simpa only [directSourceFinalCrossoverTaggedClauses,
      directSourceFinalCrossoverTaggedSourceClauses] using
      directSourceFinalCrossoverClauses_indexedMember
        decider symbols taggedClause taggedMember
  · intro taggedClause taggedMember
    exact directSourceFinalCrossoverClauses_nonempty
      decider symbols taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  · intro taggedClause taggedMember
    exact directSourceFinalCrossoverClauses_widthAtMostThree
      decider symbols taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  · exact (directSourceFinalCrossoverRouteChoices
      decider symbols).choices

end LeanTrominoes.PeriodicCNFStripReduction

end
