/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorFixed
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverRepresentativeDescriptorPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorRepresentativeSemantics

/-! # Fixed crossover prefix of public retained clause descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The public retained clause-descriptor stream begins with one fixed
Figure 8(b) descriptor block per canonical oriented crossing. -/
theorem clauseDescriptors_eq_fixedCrossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    clauseDescriptors source =
      (List.replicate
        (orientedCrossings source.incidenceGraph).length
        FormulaShapeCrossoverDirection.descriptors).flatten ++
        ((nonCrossoverMetadataNormalizedClauses source).dedup).map
          (representativeClauseDescriptor source) := by
  rw [clauseDescriptors_eq_representativeClauseDescriptors source]
  rw [representativeClauseDescriptors_eq_crossover_append_nonCrossover
    source wellFormed degree isLocal]
  rw [crossoverMetadataNormalizedClauses_dedup_map_descriptor_eq_fixed
    source wellFormed degree isLocal]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
