/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorFamily
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilySemantics

/-! # Crossover prefix of retained descriptor candidates -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The carrier, bend, routed-clause, and routed-variable candidate descriptor
families, in their retained presentation order. -/
def nonCrossoverMetadataClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  carrierMetadataClauseDescriptors source ++
    bendMetadataClauseDescriptors source ++
      routedClauseMetadataClauseDescriptors source ++
        routedVariableMetadataClauseDescriptors source

/-- The candidate descriptor list begins with the canonical descriptors of
the normalized crossover clauses. -/
theorem metadataClauseDescriptorCandidates_eq_crossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    metadataClauseDescriptorCandidates source =
      (crossoverMetadataNormalizedClauses source).map
          canonicalCrossoverClauseDescriptor ++
        nonCrossoverMetadataClauseDescriptors source := by
  rw [metadataClauseDescriptorCandidates_eq_families source]
  unfold familyMetadataClauseDescriptors
    nonCrossoverMetadataClauseDescriptors
  rw [crossoverMetadataClauseDescriptors_eq_map_canonicalDescriptor
    source wellFormed degree isLocal]
  simp only [List.append_assoc]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
