/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorCandidateLookup

/-! # Representative descriptors of normalized routed-variable clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Public first-occurrence representative selection assigns a normalized
routed-variable implication the descriptor classified by its arm and
direction. -/
theorem representativeClauseDescriptor_eq_normalizedRoutedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedLink : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) × Bool)
    (taggedLinkMember : taggedLink ∈
      ((drawingRoutedVariableLinks source).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source))).product
        [true, false]) :
    representativeClauseDescriptor source
        (PeriodicEquality.normalizedClause taggedLink) =
      normalizedRoutedVariableClauseDescriptor taggedLink := by
  have routedVariableMember :
      PeriodicEquality.normalizedClause taggedLink ∈
        routedVariableMetadataNormalizedClauses source := by
    rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
      PeriodicEquality.normalizedFormulaClauses_eq]
    exact List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  have nonCrossoverMember :
      PeriodicEquality.normalizedClause taggedLink ∈
        nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [List.mem_append]
    exact Or.inr routedVariableMember
  have normalizedMember :
      PeriodicEquality.normalizedClause taggedLink ∈
        normalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover]
    exact List.mem_append_right _ nonCrossoverMember
  have clauseLookup :
      (normalizedClauses source)[
          (normalizedClauses source).idxOf
            (PeriodicEquality.normalizedClause taggedLink)]? =
        some (PeriodicEquality.normalizedClause taggedLink) :=
    List.getElem?_idxOf normalizedMember
  have candidateLookup :=
    metadataClauseDescriptorCandidates_getElem?_eq source
      (PeriodicEquality.normalizedClause taggedLink)
      ((normalizedClauses source).idxOf
        (PeriodicEquality.normalizedClause taggedLink))
      clauseLookup
  have canonicalLookup :=
    metadataClauseDescriptorCandidates_idxOf_eq_normalizedRoutedVariable
      source wellFormed degree isLocal taggedLink taggedLinkMember
  unfold representativeClauseDescriptor
  exact Option.some.inj (candidateLookup.symm.trans canonicalLookup)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
