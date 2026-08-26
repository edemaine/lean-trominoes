/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListMappedScan
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorFixed
import LeanTrominoes.RetainedAngularFanFinalCopiedCrossoverClauseQueryAtSemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation

/-! # Exact final query semantics for the crossover family -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

private theorem crossoverFormula_length : crossoverFormula.length = 26 := by
  native_decide

/-- Fixed crossover queries indexed through the actual fixed clause list. -/
private def retainedFinalDirectCrossoverClauseQueriesByFormula :
    List RetainedFinalCopiedClauseQuery :=
  crossoverFormula.zipIdx.map fun taggedClause =>
    retainedFinalDirectCrossoverClauseQueryAt
      (Fin.ofNat 26 taggedClause.2)

private theorem
    retainedFinalDirectCrossoverClauseQueriesByFormula_eq :
    retainedFinalDirectCrossoverClauseQueriesByFormula =
      retainedFinalDirectCrossoverClauseQueries := by
  native_decide

/-- The exact globally indexed crossover prefix is one stable fixed query
block per canonical oriented crossing. -/
theorem retainedFinalCrossoverClauseQueries_formula_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ []) :
    retainedFinalIndexedClauseQueriesFrom formula 0
        (crossoverMetadataNormalizedClausesDedup formula) =
      (List.replicate
        (orientedCrossings formula.incidenceGraph).length
        retainedFinalDirectCrossoverClauseQueries).flatten := by
  have graphWellFormed :
      formula.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed formula
  have graphDegree :
      formula.incidenceGraph.DegreeAtMost 3 :=
    PeriodicCNF.incidenceGraph_degreeAtMost
      sourceWidth sourceOccurrences
  have graphLocal :
      formula.incidenceGraph.IsLocal :=
    PeriodicCNF.incidenceGraph_isLocal sourceLocal
  let crossings := canonicalizedCrossingHalo formula.incidenceGraph
  let block := @canonicalNormalizedCrossoverBlock Variable
  have blockLength : ∀ crossing, (block crossing).length = 26 := by
    intro crossing
    simp [block, canonicalNormalizedCrossoverBlock,
      crossoverFormula_length]
  have crossoverClausesEq :
      crossoverMetadataNormalizedClausesDedup formula =
        crossings.flatMap block := by
    unfold crossoverMetadataNormalizedClausesDedup
    simpa only [crossings, block] using
      crossoverMetadataNormalizedClauses_dedup_eq
        formula graphWellFormed graphDegree graphLocal
  have indexedBlocksEq :
      (crossings.flatMap block).zipIdx =
        crossings.zipIdx.flatMap fun taggedCrossing =>
          (block taggedCrossing.1).zipIdx
            (26 * taggedCrossing.2) := by
    simpa using
      IndexedListScan.flatMap_zipIdx_eq_zipIdx_flatMap_fixed_zero
        crossings block 26 0 blockLength
  have exactQueriesEq :
      retainedFinalIndexedClauseQueriesFrom formula 0
          (crossoverMetadataNormalizedClausesDedup formula) =
        crossings.zipIdx.flatMap fun _taggedCrossing =>
          retainedFinalDirectCrossoverClauseQueriesByFormula := by
    rw [crossoverClausesEq]
    unfold retainedFinalIndexedClauseQueriesFrom
    rw [indexedBlocksEq, List.map_flatMap]
    apply List.flatMap_congr
    intro taggedCrossing taggedCrossingMember
    unfold block canonicalNormalizedCrossoverBlock
      retainedFinalDirectCrossoverClauseQueriesByFormula
    rw [List.zipIdx_map, List.zipIdx_eq_map_add]
    have reindexedFixedClauses :
        crossoverFormula.zipIdx.zipIdx =
          crossoverFormula.zipIdx.map fun taggedClause =>
            (taggedClause, taggedClause.2) := by
      simpa using
        List.zipIdx_map_zipIdx crossoverFormula
          (fun taggedClause => taggedClause)
    rw [reindexedFixedClauses]
    simp only [List.map_map]
    apply List.map_congr_left
    intro fixedTaggedClause fixedTaggedClauseMember
    let normalizedClause :=
      FormulaShapeCrossoverDirection.wrappedNormalizedClause
        (Variable := Variable) taggedCrossing.1 fixedTaggedClause.1
    let globalIndex := 26 * taggedCrossing.2 + fixedTaggedClause.2
    let globalTaggedClause := (normalizedClause, globalIndex)
    have fixedGlobalMember :
        (fixedTaggedClause, globalIndex) ∈
          crossoverFormula.zipIdx.zipIdx (26 * taggedCrossing.2) := by
      rw [List.zipIdx_eq_map_add, reindexedFixedClauses,
        List.map_map]
      exact List.mem_map.mpr
        ⟨fixedTaggedClause, fixedTaggedClauseMember, rfl⟩
    have blockMember :
        globalTaggedClause ∈
          (canonicalNormalizedCrossoverBlock
            (Variable := Variable) taggedCrossing.1).zipIdx
              (26 * taggedCrossing.2) := by
      unfold canonicalNormalizedCrossoverBlock
      rw [List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(fixedTaggedClause, globalIndex), fixedGlobalMember, rfl⟩
    have indexedBlocksMember :
        globalTaggedClause ∈
          crossings.zipIdx.flatMap fun indexedCrossing =>
            (block indexedCrossing.1).zipIdx
              (26 * indexedCrossing.2) := by
      exact List.mem_flatMap.mpr
        ⟨taggedCrossing, taggedCrossingMember,
          by simpa only [block] using blockMember⟩
    have wholeCrossoverMember :
        globalTaggedClause ∈ (crossings.flatMap block).zipIdx := by
      rw [indexedBlocksEq]
      exact indexedBlocksMember
    have crossoverTaggedMember :
        globalTaggedClause ∈
          (crossoverMetadataNormalizedClausesDedup formula).zipIdx := by
      rw [crossoverClausesEq]
      exact wholeCrossoverMember
    have clauseLookup :=
      IndexedListScan.append_getElem?_of_mem_zipIdx
        (crossoverMetadataNormalizedClausesDedup formula)
        (nonCrossoverMetadataNormalizedClausesDedup formula)
        globalTaggedClause crossoverTaggedMember
    rw [← deduplicatedClauses_eq_named_crossover_append_nonCrossover
      formula graphWellFormed graphDegree graphLocal] at clauseLookup
    let witness : CrossoverClauseWitness normalizedClause := {
      crossing := taggedCrossing.1
      taggedClause := fixedTaggedClause
      taggedClauseMember := fixedTaggedClauseMember
      clauseEqual := rfl
    }
    have localQueryEq :=
      retainedFinalCopiedClauseQueryOfLiterals_eq_crossoverAt_of_witness
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty globalIndex normalizedClause
        clauseLookup
        (List.fst_mem_of_mem_zipIdx crossoverTaggedMember)
        witness
    have localIndexLt : fixedTaggedClause.2 < 26 := by
      have indexLt :=
        List.snd_lt_of_mem_zipIdx fixedTaggedClauseMember
      rw [crossoverFormula_length] at indexLt
      exact indexLt
    have boundedIndexEq :
        (⟨fixedTaggedClause.2, localIndexLt⟩ : Fin 26) =
          Fin.ofNat 26 fixedTaggedClause.2 := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt localIndexLt]
    change
      retainedFinalCopiedClauseQueryOfLiterals formula
          (26 * taggedCrossing.2 + fixedTaggedClause.2)
          (FormulaShapeCrossoverDirection.wrappedNormalizedClause
            taggedCrossing.1 fixedTaggedClause.1) =
        retainedFinalDirectCrossoverClauseQueryAt
          (Fin.ofNat 26 fixedTaggedClause.2)
    simpa only [normalizedClause, globalIndex, witness,
      boundedIndexEq] using localQueryEq
  rw [exactQueriesEq,
    retainedFinalDirectCrossoverClauseQueriesByFormula_eq]
  have constantBlocks (values : List CrossingRecord) (start : Nat) :
      (values.zipIdx start).flatMap (fun _ =>
          retainedFinalDirectCrossoverClauseQueries) =
        (List.replicate values.length
          retainedFinalDirectCrossoverClauseQueries).flatten := by
    induction values generalizing start with
    | nil => rfl
    | cons value values induction =>
        simp only [List.zipIdx_cons, List.flatMap_cons,
          List.length_cons, List.replicate_succ, List.flatten_cons]
        exact congrArg
          (List.append retainedFinalDirectCrossoverClauseQueries)
          (induction (start + 1))
  rw [constantBlocks crossings 0]
  rw [canonicalizedCrossingHalo_length
    graphWellFormed graphDegree graphLocal]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
