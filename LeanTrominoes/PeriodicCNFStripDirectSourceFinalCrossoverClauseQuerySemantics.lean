/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilies
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets
import LeanTrominoes.RetainedAngularFanFinalCopiedCrossoverClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedDirectnessPredicates
import LeanTrominoes.RetainedAngularFanFinalDirectCrossoverQueryDirectness

/-! # Exact final crossover queries of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverQueryExactStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverQueryExactVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled crossover query prefix is the exact globally indexed
query scan over the named crossover clause family. -/
theorem directRetainedFinalCrossoverClauseQueries_eq_indexed
    (symbols : List encoding.Γ) :
    directRetainedFinalCrossoverClauseQueries decider symbols =
      retainedFinalIndexedClauseQueriesFrom
        (directSourceFormula decider symbols) 0
        (directSourceFinalCrossoverClauses decider symbols) := by
  let original := PolySpaceCompiler.formulaOfSymbols decider symbols
  let source := PeriodicThreeCNF.formula original
  let formula := PeriodicThreeSATThree.formula source
  have sourceLocal : source.IsLocal :=
    PeriodicThreeCNF.formula_isLocal
      (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  have sourceWidth : source.WidthAtMost 3 :=
    PeriodicThreeCNF.formula_widthAtMostThree original
  have sourceClausesNonempty : ∀ clause ∈ source.clauses,
      clause ≠ [] :=
    PeriodicThreeCNF.formula_clausesNonempty original
      (formulaOfSymbols_clauses_nonempty decider symbols)
  have sourceEq : directSourceFormula decider symbols = formula := by
    simpa only [formula, source, original] using
      directSourceFormula_eq_threeSATThree decider symbols
  have semantic :=
    retainedFinalCrossoverClauseQueries_formula_eq
      formula
      (PeriodicThreeSATThree.formula_isLocal sourceLocal)
      (PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth)
      (PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq
        source)
      (PeriodicThreeSATThree.formula_clausesNonempty
        source sourceClausesNonempty)
  unfold directRetainedFinalCrossoverClauseQueries
    directSourceFinalCrossoverClauses
    directThreeCNFSourceFormula
  rw [sourceEq]
  simpa only [formula, source, original] using semantic.symm

/-- Consequently every exact indexed query in the crossover prefix is
all-direct. -/
theorem directSourceFinalIndexedCrossoverClauseQueries_allDirect
    (symbols : List encoding.Γ) :
    ∀ query ∈ retainedFinalIndexedClauseQueriesFrom
        (directSourceFormula decider symbols) 0
        (directSourceFinalCrossoverClauses decider symbols),
      query.AllDirect := by
  intro query queryMember
  rw [← directRetainedFinalCrossoverClauseQueries_eq_indexed]
    at queryMember
  unfold directRetainedFinalCrossoverClauseQueries at queryMember
  rcases List.mem_flatten.mp queryMember with
    ⟨block, blockMember, queryMember⟩
  have blockEq :
      block = retainedFinalDirectCrossoverClauseQueries :=
    (List.mem_replicate.mp blockMember).2
  subst block
  exact retainedFinalDirectCrossoverClauseQueries_allDirect
    query queryMember

/-- Predicate-packaged form of exact crossover query directness. -/
theorem directSourceFinalIndexedCrossoverClauseQueriesAllDirect
    (symbols : List encoding.Γ) :
    FinalIndexedClauseQueriesAllDirect
      (directSourceFormula decider symbols) 0
      (directSourceFinalCrossoverClauses decider symbols) :=
  ⟨directSourceFinalIndexedCrossoverClauseQueries_allDirect
    decider symbols⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
