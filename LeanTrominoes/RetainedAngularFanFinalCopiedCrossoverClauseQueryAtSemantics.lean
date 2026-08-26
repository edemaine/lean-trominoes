/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorFunction
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverDescriptor
import LeanTrominoes.RetainedAngularFanDirectSourceCrossoverChoiceShape
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseDirectMetadataQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCrossoverMetadataSemantics

/-! # Exact final query for one crossover clause -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

private theorem crossoverFormula_length : crossoverFormula.length = 26 := by
  native_decide

/-- The exact final query at a canonical crossover clause is its stable
direct query at the same local Figure 8(b) clause index. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_eq_crossoverAt_of_witness
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (crossoverMember :
      clause ∈ crossoverMetadataNormalizedClausesDedup formula)
    (witness : CrossoverClauseWitness clause) :
    retainedFinalCopiedClauseQueryOfLiterals
        formula clauseIndex clause =
      retainedFinalDirectCrossoverClauseQueryAt
        ⟨witness.taggedClause.2, by
          have indexLt :=
            List.snd_lt_of_mem_zipIdx witness.taggedClauseMember
          rw [crossoverFormula_length] at indexLt
          exact indexLt⟩ := by
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
  rcases
      exists_finalCrossoverMetadata_of_clause_lookup
        formula clauseIndex clause clauseLookup crossoverMember with
    ⟨metadata, metadataLookup, normalizedEq, crossing,
      taggedClause, crossingMember, taggedClauseMember, metadataEq⟩
  subst metadata
  let physicalWitness : CrossoverClauseWitness clause := {
    crossing := crossing.periodNormalize formula.incidenceGraph
    taggedClause := taggedClause
    taggedClauseMember := taggedClauseMember
    clauseEqual := by
      exact
        (normalizedClause_crossoverClauseAt_eq
            formula graphWellFormed graphDegree graphLocal
            crossing crossingMember taggedClause.1 taggedClause.2).symm.trans
          normalizedEq
  }
  have taggedClauseEq : taggedClause = witness.taggedClause :=
    (CrossoverClauseWitness.unique physicalWitness witness).2
  subst taggedClause
  have localClauseIndexLt : witness.taggedClause.2 < 26 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx witness.taggedClauseMember
    rw [crossoverFormula_length] at indexLt
    exact indexLt
  let localClauseIndex : Fin 26 :=
    ⟨witness.taggedClause.2, localClauseIndexLt⟩
  have queryEq :=
    retainedFinalCopiedClauseQueryOfLiterals_eq_directOfMetadataDescriptor
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex clause clauseLookup
      ⟨crossoverClauseAt crossing witness.taggedClause.1,
        .crossover crossing witness.taggedClause.2⟩
      metadataLookup normalizedEq
      (Or.inl ⟨crossing, witness.taggedClause.2, rfl⟩)
      (.crossover localClauseIndex) (by
        intro literalIndex rawChoice rawLookup
        rcases
            retainedDirectSourceRouteChoice?_crossover_eq_some_iff_shape
              formula crossing witness.taggedClause.2 literalIndex
              rawChoice rawLookup with
          ⟨localClauseIndexBound, literalIndexBound, rawChoiceEq⟩
        subst rawChoice
        exact ⟨rfl, rfl⟩)
  have metadataDescriptorEq :
      metadataClauseDescriptor formula
          ⟨crossoverClauseAt crossing witness.taggedClause.1,
            .crossover crossing witness.taggedClause.2⟩ =
        FormulaShapeCrossoverDirection.descriptorAt
          witness.taggedClause := by
    simpa [FormulaShapeCrossoverDirection.descriptorAt] using
      metadataClauseDescriptor_crossoverClauseAt_eq
        formula graphWellFormed graphDegree graphLocal
        crossing crossingMember witness.taggedClause.1
        witness.taggedClause.2
  have descriptorLookup :
      FormulaShapeCrossoverDirection.descriptors[
          witness.taggedClause.2]? =
        some (FormulaShapeCrossoverDirection.descriptorAt
          witness.taggedClause) := by
    have taggedClauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp witness.taggedClauseMember
    have taggedZipLookup :
        crossoverFormula.zipIdx[witness.taggedClause.2]? =
          some witness.taggedClause := by
      rw [List.getElem?_zipIdx]
      simpa using congrArg
        (fun value => value.map fun clause =>
          (clause, witness.taggedClause.2))
        taggedClauseLookup
    rw [FormulaShapeCrossoverDirection.descriptors_eq_map_descriptorAt,
      List.getElem?_map]
    exact congrArg
      (Option.map FormulaShapeCrossoverDirection.descriptorAt)
      taggedZipLookup
  have descriptorGetD :
      FormulaShapeCrossoverDirection.descriptors.getD
          witness.taggedClause.2 default =
        FormulaShapeCrossoverDirection.descriptorAt
          witness.taggedClause := by
    rw [List.getD_eq_getElem?_getD, descriptorLookup]
    rfl
  calc
    retainedFinalCopiedClauseQueryOfLiterals
          formula clauseIndex clause =
        RetainedFinalCopiedClauseQuery.directOfToken
          (.crossover localClauseIndex)
          (metadataClauseDescriptor formula
            ⟨crossoverClauseAt crossing witness.taggedClause.1,
              .crossover crossing witness.taggedClause.2⟩) :=
      queryEq
    _ = RetainedFinalCopiedClauseQuery.directOfToken
          (.crossover localClauseIndex)
          (FormulaShapeCrossoverDirection.descriptorAt
            witness.taggedClause) := by
      rw [metadataDescriptorEq]
    _ = retainedFinalDirectCrossoverClauseQueryAt
          localClauseIndex := by
      unfold retainedFinalDirectCrossoverClauseQueryAt
      rw [descriptorGetD]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
