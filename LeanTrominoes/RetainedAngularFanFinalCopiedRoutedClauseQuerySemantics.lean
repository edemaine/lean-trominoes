/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedClauseDescriptorLookup
import LeanTrominoes.PeriodicThreeSATThreeRoutedClauseLookup
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedClauseQueryAtSemantics

/-! # Exact final query semantics for the routed-clause family -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

local instance finalRoutedClauseQueryThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The exact globally indexed routed-clause family is one stable direct
query per clause of the occurrence-split formula, in its source presentation
order. -/
theorem retainedFinalRoutedClauseQueries_formula_eq
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
      ((crossoverMetadataNormalizedClausesDedup formula).length +
        (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
          source).length) +
      (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
        source).length
    retainedFinalIndexedClauseQueriesFrom formula start
        (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
          source) =
      formula.clauses.map fun clause =>
        retainedFinalDirectRoutedClauseQuery
          (clause.map fun literal =>
            (⟨false, literal.value⟩ :
              UnaryProgramClauseProfile.LiteralProfile)) := by
  dsimp only
  let formula := PeriodicThreeSATThree.formula source
  let start :=
    ((crossoverMetadataNormalizedClausesDedup formula).length +
      (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
        source).length) +
    (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source).length
  have formulaLocal : formula.IsLocal :=
    PeriodicThreeSATThree.formula_isLocal sourceLocal
  have formulaWidth : formula.WidthAtMost 3 :=
    PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth
  have formulaOccurrences :=
    PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source
  have formulaClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [] :=
    PeriodicThreeSATThree.formula_clausesNonempty
      source sourceClausesNonempty
  have formulaWellFormed : formula.incidenceGraph.IsWellFormed :=
    PeriodicThreeSATThree.formula_incidenceGraph_isWellFormed source
  have indexedBaseEq :
      (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
          source).zipIdx start =
        formula.clauses.zipIdx.map fun taggedClause =>
          (normalizedRoutedClauseAt formula
            (taggedClause.2, (0, 0)), start + taggedClause.2) := by
    unfold PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
      baseRoutedClauseNormalizedClauses
    rw [List.zipIdx_eq_map_add,
      List.zipIdx_map_zipIdx, List.map_map]
    apply List.map_congr_left
    intro taggedClause _taggedClauseMember
    simp [formula, Nat.add_comm]
  have targetEq :
      formula.clauses.map (fun clause =>
          retainedFinalDirectRoutedClauseQuery
            (clause.map fun literal =>
              (⟨false, literal.value⟩ :
                UnaryProgramClauseProfile.LiteralProfile))) =
        formula.clauses.zipIdx.map fun taggedClause =>
          retainedFinalDirectRoutedClauseQuery
            (taggedClause.1.map fun literal =>
              (⟨false, literal.value⟩ :
                UnaryProgramClauseProfile.LiteralProfile)) := by
    let emit := fun clause : PeriodicClause
        (ThreeOccurrenceVariable Variable) =>
      retainedFinalDirectRoutedClauseQuery
        (clause.map fun literal =>
          (⟨false, literal.value⟩ :
            UnaryProgramClauseProfile.LiteralProfile))
    calc
      formula.clauses.map emit =
          (formula.clauses.zipIdx.map Prod.fst).map emit :=
        congrArg (List.map emit)
          (List.zipIdx_map_fst 0 formula.clauses).symm
      _ = _ := by
        rw [List.map_map]
        rfl
  unfold retainedFinalIndexedClauseQueriesFrom
  rw [indexedBaseEq, targetEq, List.map_map]
  apply List.map_congr_left
  intro taggedClause taggedClauseMember
  let normalizedClause :=
    normalizedRoutedClauseAt formula (taggedClause.2, (0, 0))
  let globalIndex := start + taggedClause.2
  let globalTaggedClause := (normalizedClause, globalIndex)
  have baseTaggedMember : globalTaggedClause ∈
      (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
        source).zipIdx start := by
    rw [indexedBaseEq]
    exact List.mem_map.mpr
      ⟨taggedClause, taggedClauseMember, rfl⟩
  have clauseLookup :
      (deduplicatedClauses formula)[globalIndex]? =
        some normalizedClause := by
    simpa only [formula, start, globalTaggedClause] using
      PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses_getElem?_of_mem_zipIdx
        source sourceLocal sourceWidth sourceClausesNonempty
        positiveOffsets globalTaggedClause baseTaggedMember
  have taggedSiteMember :
      (taggedClause, (0, 0)) ∈
        formula.clauses.zipIdx.product neighborTranslations := by
    apply List.mem_product.mpr
    exact ⟨taggedClauseMember, by native_decide⟩
  have routedClauseMember :
      normalizedClause ∈
        routedClauseMetadataNormalizedClauses formula := by
    rw [routedClauseMetadataNormalizedClauses_eq_map_taggedSites]
    exact List.mem_map.mpr
      ⟨(taggedClause, (0, 0)), taggedSiteMember, rfl⟩
  have localQueryEq :=
    retainedFinalCopiedClauseQueryOfLiterals_eq_routedClause_of_mem
      formula formulaLocal formulaWidth formulaOccurrences
      formulaClausesNonempty globalIndex normalizedClause
      clauseLookup routedClauseMember
  have profilesEq :
      normalizedClause.map
          FormulaShapeDirectionOrdering.literalProfile =
        taggedClause.1.map fun literal =>
          (⟨false, literal.value⟩ :
            UnaryProgramClauseProfile.LiteralProfile) := by
    calc
      _ = routedClauseCurrentProfiles formula
            (taggedClause.2, (0, 0)) :=
        normalizedRoutedClauseAt_literalProfiles_eq_current
          formula formulaWellFormed (taggedClause.2, (0, 0))
      _ = _ :=
        routedClauseCurrentProfiles_eq_taggedClause
          formula taggedClause taggedClauseMember (0, 0)
  change
    retainedFinalCopiedClauseQueryOfLiterals
        formula globalIndex normalizedClause =
      retainedFinalDirectRoutedClauseQuery
        (taggedClause.1.map fun literal =>
          (⟨false, literal.value⟩ :
            UnaryProgramClauseProfile.LiteralProfile))
  rw [localQueryEq, profilesEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
