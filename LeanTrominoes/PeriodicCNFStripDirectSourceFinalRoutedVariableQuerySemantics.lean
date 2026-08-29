/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedVariableClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFacts
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedDirectnessPredicates
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedVariableClauseQueryCorrectness
import LeanTrominoes.RetainedAngularFanFinalDirectRoutedVariableQueryDirectness

/-! # Exact final routed-variable queries of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableQueryExactStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedVariableQueryExactVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The routed-variable suffix, with its global clause indices, packaged as a
concrete query column. -/
def directSourceFinalIndexedRoutedVariableQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let start :=
    (((PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.crossoverMetadataNormalizedClausesDedup
            formula).length +
        (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
          source).length) +
      (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source).length) +
    (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
      source).length
  retainedFinalIndexedClauseQueriesFrom formula start
    (PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
      source)

/-- The semantic suffix uses the named formula, start, and clause family. -/
theorem directSourceFinalIndexedRoutedVariableQueries_eq_named
    (symbols : List encoding.Γ) :
    directSourceFinalIndexedRoutedVariableQueries decider symbols =
      retainedFinalIndexedClauseQueriesFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalRoutedVariableStart decider symbols)
        (directSourceFinalRoutedVariableClauses decider symbols) := by
  rfl

/-- Direct specialization of the generic routed-variable query theorem in
its native `let`-bound form. -/
theorem directThreeCNFSourceFinalRoutedVariableQueries_formula_eq
    (symbols : List encoding.Γ) :
    let source := directThreeCNFSourceFormula decider symbols
    let formula := PeriodicThreeSATThree.formula source
    let start :=
      (((PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.crossoverMetadataNormalizedClausesDedup
              formula).length +
          (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
            source).length) +
        (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
          source).length) +
      (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
        source).length
    retainedFinalIndexedClauseQueriesFrom formula start
        (PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
          source) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex =>
          retainedFinalDirectRoutedVariableFullSiteQueries) := by
  have occurrenceDecidableEqEq :
      directFinalRoutedVariableQueryExactVariableDecidableEq =
        (PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq :
          DecidableEq Variable) :=
    Subsingleton.elim _ _
  rw [occurrenceDecidableEqEq]
  exact retainedFinalRoutedVariableClauseQueries_formula_eq_fullSites
    (directThreeCNFSourceFormula decider symbols)
    (directThreeCNFSource_isLocal decider symbols)
    (directThreeCNFSource_widthAtMostThree decider symbols)
    (directThreeCNFSource_clausesNonempty decider symbols)
    (directThreeCNFSource_positiveOffsets decider symbols)

/-- The concrete indexed suffix is exactly the fixed six-query block stream
used by the direct compiler. -/
theorem directSourceFinalIndexedRoutedVariableQueries_eq_fullSites
    (symbols : List encoding.Γ) :
    directSourceFinalIndexedRoutedVariableQueries decider symbols =
      (List.range (PeriodicCNF.presentationLiteralCount
        (directThreeCNFSourceFormula decider symbols))).flatMap
          (fun _targetIndex =>
            retainedFinalDirectRoutedVariableFullSiteQueries) := by
  unfold directSourceFinalIndexedRoutedVariableQueries
  exact directThreeCNFSourceFinalRoutedVariableQueries_formula_eq
    decider symbols

/-- The compiled routed-variable query suffix is the exact globally indexed
scan over the named routed-variable clause family. -/
theorem directRetainedFinalRoutedVariableClauseQueries_eq_indexed
    (symbols : List encoding.Γ) :
    directRetainedFinalRoutedVariableClauseQueries decider symbols =
      directSourceFinalIndexedRoutedVariableQueries decider symbols := by
  unfold directRetainedFinalRoutedVariableClauseQueries
  simpa only [directThreeCNFSourceFormula] using
    (directSourceFinalIndexedRoutedVariableQueries_eq_fullSites
      decider symbols).symm

/-- Every exact indexed routed-variable query is direct. -/
theorem directSourceFinalIndexedRoutedVariableQueries_allDirect
    (symbols : List encoding.Γ) :
    ∀ query ∈
        directSourceFinalIndexedRoutedVariableQueries decider symbols,
      query.AllDirect := by
  intro query queryMember
  rw [← directRetainedFinalRoutedVariableClauseQueries_eq_indexed]
    at queryMember
  unfold directRetainedFinalRoutedVariableClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨_targetIndex, _targetIndexMember, queryMember⟩
  exact retainedFinalDirectRoutedVariableFullSiteQueries_allDirect
    query queryMember

/-- Predicate-packaged form of exact routed-variable directness. -/
theorem directSourceFinalIndexedRoutedVariableQueriesAllDirect
    (symbols : List encoding.Γ) :
    FinalIndexedClauseQueriesAllDirect
      (directSourceFinalNormalizedFormula decider symbols)
      (directSourceFinalRoutedVariableStart decider symbols)
      (directSourceFinalRoutedVariableClauses decider symbols) :=
  ⟨by
    rw [← directSourceFinalIndexedRoutedVariableQueries_eq_named]
    exact directSourceFinalIndexedRoutedVariableQueries_allDirect
      decider symbols⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
