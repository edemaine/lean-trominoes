/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseWitness

/-! # Descriptor function on normalized crossover clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

namespace FormulaShapeCrossoverDirection

/-- The fixed descriptor attached to one tagged Figure 8(b) clause. -/
def descriptorAt
    (taggedClause : EmbeddedClause CrossoverVariable × Nat) :
    FormulaShapeDirectionOrdering.Token :=
  .clause
    (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
      crossoverStraightIncidenceDrawing.routes taggedClause.2
      ⟨(0, 0), zeroOffsetClause taggedClause.1⟩)

theorem descriptors_eq_map_descriptorAt :
    descriptors = crossoverFormula.zipIdx.map descriptorAt :=
  rfl

end FormulaShapeCrossoverDirection

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Read the fixed descriptor of a normalized crossover clause from its
unique canonical witness; return the variable marker outside that domain. -/
def canonicalCrossoverClauseDescriptor
    {Variable : Type} [DecidableEq Variable]
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :
    FormulaShapeDirectionOrdering.Token := by
  classical
  exact
    if witness : Nonempty (CrossoverClauseWitness clause) then
      FormulaShapeCrossoverDirection.descriptorAt
        (Classical.choice witness).taggedClause
    else
      .variable

/-- Every supplied witness computes the same canonical descriptor. -/
theorem canonicalCrossoverClauseDescriptor_eq_of_witness
    {Variable : Type} [DecidableEq Variable]
    {clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)}
    (witness : CrossoverClauseWitness clause) :
    canonicalCrossoverClauseDescriptor clause =
      FormulaShapeCrossoverDirection.descriptorAt
        witness.taggedClause := by
  unfold canonicalCrossoverClauseDescriptor
  rw [dif_pos ⟨witness⟩]
  have unique :=
    CrossoverClauseWitness.unique
      (Classical.choice
        (show Nonempty (CrossoverClauseWitness clause) from ⟨witness⟩))
      witness
  rw [unique.2]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
