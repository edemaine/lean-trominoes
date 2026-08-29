/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedClauseQuerySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFacts
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedDirectnessPredicates
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalDirectClauseQueryTemplateDirectness

/-! # Exact final routed-clause queries of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseQueryExactStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedClauseQueryExactVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The named routed-clause family, with its global indices, packaged as a
concrete query column. -/
def directSourceFinalIndexedRoutedClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let start :=
    ((PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.crossoverMetadataNormalizedClausesDedup
          formula).length +
      (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
        source).length) +
    (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source).length
  retainedFinalIndexedClauseQueriesFrom formula start
    (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
      source)

/-- The semantic query column uses the named formula, start, and clause
family introduced for the final five-family presentation. -/
theorem directSourceFinalIndexedRoutedClauseQueries_eq_named
    (symbols : List encoding.Γ) :
    directSourceFinalIndexedRoutedClauseQueries decider symbols =
      retainedFinalIndexedClauseQueriesFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalRoutedClauseStart decider symbols)
        (directSourceFinalRoutedClauseClauses decider symbols) := by
  rfl

/-- Direct specialization of the generic routed-clause semantic theorem,
kept in its native `let`-bound form. -/
theorem directThreeCNFSourceFinalRoutedClauseQueries_formula_eq
    (symbols : List encoding.Γ) :
    let source := directThreeCNFSourceFormula decider symbols
    let formula := PeriodicThreeSATThree.formula source
    let start :=
      ((PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.crossoverMetadataNormalizedClausesDedup
            formula).length +
        (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
          source).length) +
      (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source).length
    retainedFinalIndexedClauseQueriesFrom formula start
        (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
          source) =
      formula.clauses.map fun clause =>
        retainedFinalDirectRoutedClauseQuery
          (clause.map fun literal =>
            (⟨false, literal.value⟩ :
              UnaryProgramClauseProfile.LiteralProfile)) := by
  have occurrenceDecidableEqEq :
      directFinalRoutedClauseQueryExactVariableDecidableEq =
        (PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq :
          DecidableEq Variable) :=
    Subsingleton.elim _ _
  rw [occurrenceDecidableEqEq]
  exact retainedFinalRoutedClauseQueries_formula_eq
    (directThreeCNFSourceFormula decider symbols)
    (directThreeCNFSource_isLocal decider symbols)
    (directThreeCNFSource_widthAtMostThree decider symbols)
    (directThreeCNFSource_clausesNonempty decider symbols)
    (directThreeCNFSource_positiveOffsets decider symbols)

/-- The concrete indexed routed-clause scan has the source-clause template
presentation supplied by the generic five-family semantics. -/
theorem directSourceFinalIndexedRoutedClauseQueries_eq_sourceClauses
    (symbols : List encoding.Γ) :
    directSourceFinalIndexedRoutedClauseQueries decider symbols =
      (directSourceFinalNormalizedFormula decider symbols).clauses.map
        fun clause =>
        retainedFinalDirectRoutedClauseQuery
          (clause.map fun literal =>
            (⟨false, literal.value⟩ :
              UnaryProgramClauseProfile.LiteralProfile)) := by
  unfold directSourceFinalIndexedRoutedClauseQueries
    directSourceFinalNormalizedFormula
  exact directThreeCNFSourceFinalRoutedClauseQueries_formula_eq
    decider symbols

/-- The compiled routed-clause queries are the exact globally indexed scan
over the named routed-clause family. -/
theorem directRetainedFinalRoutedClauseQueries_eq_indexed
    (symbols : List encoding.Γ) :
    directRetainedFinalRoutedClauseQueries decider symbols =
      directSourceFinalIndexedRoutedClauseQueries decider symbols := by
  have compiledNormalized :
      directRetainedFinalRoutedClauseQueries decider symbols =
        (directSourceFinalNormalizedFormula decider symbols).clauses.map
          fun clause =>
            retainedFinalDirectRoutedClauseQuery
              (clause.map fun literal =>
                (⟨false, literal.value⟩ :
                  UnaryProgramClauseProfile.LiteralProfile)) := by
    rw [directRetainedFinalRoutedClauseQueries_eq_sourceClauses,
      directSourceFormula_eq_finalNormalized]
  exact compiledNormalized.trans
    (directSourceFinalIndexedRoutedClauseQueries_eq_sourceClauses
      decider symbols).symm

/-- Every exact indexed routed-clause query is direct. -/
theorem directSourceFinalIndexedRoutedClauseQueries_allDirect
    (symbols : List encoding.Γ) :
    ∀ query ∈
        directSourceFinalIndexedRoutedClauseQueries decider symbols,
      query.AllDirect := by
  intro query queryMember
  rw [← directRetainedFinalRoutedClauseQueries_eq_indexed]
    at queryMember
  rw [directRetainedFinalRoutedClauseQueries_eq_sourceClauses]
    at queryMember
  rcases List.mem_map.mp queryMember with
    ⟨clause, _clauseMember, rfl⟩
  exact retainedFinalDirectRoutedClauseQuery_allDirect _

/-- Predicate-packaged form of exact routed-clause query directness. -/
theorem directSourceFinalIndexedRoutedClauseQueriesAllDirect
    (symbols : List encoding.Γ) :
    FinalIndexedClauseQueriesAllDirect
      (directSourceFinalNormalizedFormula decider symbols)
      (directSourceFinalRoutedClauseStart decider symbols)
      (directSourceFinalRoutedClauseClauses decider symbols) :=
  ⟨by
    rw [← directSourceFinalIndexedRoutedClauseQueries_eq_named]
    exact directSourceFinalIndexedRoutedClauseQueries_allDirect
      decider symbols⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
