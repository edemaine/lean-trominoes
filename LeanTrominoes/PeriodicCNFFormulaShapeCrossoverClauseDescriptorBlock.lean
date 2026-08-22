/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorFunction

/-! # Descriptors of a normalized crossover block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Mapping the semantic descriptor function over one canonical normalized
crossover block recovers the fixed Figure 8(b) descriptor block. -/
theorem canonicalNormalizedCrossoverBlock_map_descriptor
    {Variable : Type} [DecidableEq Variable]
    (crossing : CrossingRecord) :
    (canonicalNormalizedCrossoverBlock
      (Variable := Variable) crossing).map
        canonicalCrossoverClauseDescriptor =
      FormulaShapeCrossoverDirection.descriptors := by
  rw [FormulaShapeCrossoverDirection.descriptors_eq_map_descriptorAt]
  unfold canonicalNormalizedCrossoverBlock
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedClause taggedClauseMember
  exact canonicalCrossoverClauseDescriptor_eq_of_witness
    { crossing := crossing
      taggedClause := taggedClause
      taggedClauseMember := taggedClauseMember
      clauseEqual := rfl }

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
