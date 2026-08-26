/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListSubfamilyLookup
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedVariableClauseQueryAtSemantics

/-! # Exact final routed-variable pair-list query semantics -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- An explicitly presented suffix of normalized routed-variable link clauses
produces the corresponding stable direct query at every indexed position. -/
theorem retainedFinalIndexedRoutedVariablePairQueries_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (clausePrefix :
      List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (taggedLinks : List (PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) × Bool))
    (clausesEq :
      deduplicatedClauses formula =
        clausePrefix ++ taggedLinks.map PeriodicEquality.normalizedClause)
    (taggedLinksRaw :
      ∀ taggedLink ∈ taggedLinks,
        taggedLink ∈
          ((drawingRoutedVariableLinks formula).map
            (PeriodicEquality.normalizeLink
              (externalWrappedVariableNormalization formula))).product
            [true, false]) :
    retainedFinalIndexedClauseQueriesFrom formula clausePrefix.length
        (taggedLinks.map PeriodicEquality.normalizedClause) =
      taggedLinks.map fun taggedLink =>
        retainedFinalDirectRoutedVariableClauseQuery
          (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
          false taggedLink.2 := by
  have indexedClausesEq :
      (taggedLinks.map PeriodicEquality.normalizedClause).zipIdx
          clausePrefix.length =
        (taggedLinks.zipIdx clausePrefix.length).map (fun indexedLink =>
          (PeriodicEquality.normalizedClause indexedLink.1,
            indexedLink.2)) := by
    rw [List.zipIdx_map]
    rfl
  have targetEq :
      taggedLinks.map (fun taggedLink =>
          retainedFinalDirectRoutedVariableClauseQuery
            (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
            false taggedLink.2) =
        (taggedLinks.zipIdx clausePrefix.length).map (fun indexedLink =>
          retainedFinalDirectRoutedVariableClauseQuery
            (wrappedNormalizedRoutedVariableLinkArm indexedLink.1.1)
            false indexedLink.1.2) := by
    let emit := fun taggedLink :
        PeriodicEquality.NormalizedLink
          (WrappedPeriodicPlanarSATVariable Variable) × Bool =>
      retainedFinalDirectRoutedVariableClauseQuery
        (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
        false taggedLink.2
    calc
      taggedLinks.map emit =
          ((taggedLinks.zipIdx clausePrefix.length).map Prod.fst).map emit :=
        congrArg (List.map emit)
          (List.zipIdx_map_fst clausePrefix.length taggedLinks).symm
      _ = _ := by
        rw [List.map_map]
        rfl
  unfold retainedFinalIndexedClauseQueriesFrom
  rw [indexedClausesEq, targetEq, List.map_map]
  apply List.map_congr_left
  intro indexedLink indexedLinkMember
  let taggedLink := indexedLink.1
  let clause := PeriodicEquality.normalizedClause taggedLink
  let globalIndex := indexedLink.2
  let globalTaggedClause := (clause, globalIndex)
  have familyTaggedMember : globalTaggedClause ∈
      (taggedLinks.map PeriodicEquality.normalizedClause).zipIdx
        clausePrefix.length := by
    rw [indexedClausesEq]
    exact List.mem_map.mpr
      ⟨indexedLink, indexedLinkMember, rfl⟩
  have clauseLookup :
      (deduplicatedClauses formula)[globalIndex]? = some clause := by
    exact IndexedListScan.getElem?_of_eq_append_middle_of_mem_zipIdx
      (deduplicatedClauses formula) clausePrefix
      (taggedLinks.map PeriodicEquality.normalizedClause) []
      (by simpa only [List.append_nil] using clausesEq)
      globalTaggedClause familyTaggedMember
  have taggedLinkMember : taggedLink ∈ taggedLinks :=
    List.fst_mem_of_mem_zipIdx indexedLinkMember
  have localQueryEq :=
    retainedFinalCopiedClauseQueryOfLiterals_eq_routedVariable_of_link
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty globalIndex taggedLink
      (taggedLinksRaw taggedLink taggedLinkMember) clauseLookup
  change
    retainedFinalCopiedClauseQueryOfLiterals
        formula globalIndex clause =
      retainedFinalDirectRoutedVariableClauseQuery
        (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
        false taggedLink.2
  exact localQueryEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
