/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeFiveFamilyNormalizedClauses
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedClauses
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedVariablePairQuerySemantics

/-! # Exact final query semantics for the routed-variable family -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

local instance finalRoutedVariableQueryThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The exact globally indexed routed-variable suffix is the stable direct
query map over the canonical normalized link/direction pairs. -/
theorem retainedFinalRoutedVariableClauseQueries_formula_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈
      PeriodicThreeSATThree.occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let formula := PeriodicThreeSATThree.formula source
    let start :=
      (((crossoverMetadataNormalizedClausesDedup formula).length +
        (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
          source).length) +
        (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
          source).length) +
      (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
        source).length
    retainedFinalIndexedClauseQueriesFrom formula start
        (PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
          source) =
      ((PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableLinks
          source).product [true, false]).map fun taggedLink =>
        retainedFinalDirectRoutedVariableClauseQuery
          (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
          false taggedLink.2 := by
  dsimp only
  let formula := PeriodicThreeSATThree.formula source
  let taggedLinks :=
    (PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableLinks
      source).product [true, false]
  let clausePrefix :=
    ((crossoverMetadataNormalizedClausesDedup formula ++
      PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
        source) ++
      PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source) ++
      PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses source
  have clausesEq :
      deduplicatedClauses formula =
        clausePrefix ++ taggedLinks.map PeriodicEquality.normalizedClause := by
    have fiveFamilies :=
      PeriodicThreeSATThree.deduplicatedClauses_formula_eq_routedClauseFamily
        source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
    simpa only [formula, clausePrefix, taggedLinks,
      PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses,
      PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableClauses] using
      fiveFamilies
  have taggedLinksRaw : ∀ taggedLink ∈ taggedLinks,
      taggedLink ∈
        ((drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink
            (externalWrappedVariableNormalization formula))).product
          [true, false] := by
    intro taggedLink taggedLinkMember
    rcases List.mem_product.mp taggedLinkMember with
      ⟨normalizedLinkMember, directionMember⟩
    exact List.mem_product.mpr
      ⟨by
        simpa only [formula] using
          PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableLinks_subset_raw
            source positiveOffsets normalizedLinkMember,
        directionMember⟩
  have queryEq :=
    retainedFinalIndexedRoutedVariablePairQueries_eq
      formula
      (PeriodicThreeSATThree.formula_isLocal sourceLocal)
      (PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth)
      (PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source)
      (PeriodicThreeSATThree.formula_clausesNonempty
        source sourceClausesNonempty)
      clausePrefix taggedLinks clausesEq taggedLinksRaw
  simpa only [formula, clausePrefix, taggedLinks, List.length_append,
    PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses,
    PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableClauses] using
    queryEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
