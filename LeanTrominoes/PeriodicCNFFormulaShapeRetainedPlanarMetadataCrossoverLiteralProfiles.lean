/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverClauseNormalization

/-! # Literal profiles of retained crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Opaque wrapping and canonical crossover atom names do not affect the
finite offset/polarity profile of a fixed zero-offset clause. -/
theorem wrappedNormalizedClause_literalProfiles_eq
    {Variable : Type}
    (crossing : CrossingRecord)
    (clause : EmbeddedClause CrossoverVariable) :
    (FormulaShapeCrossoverDirection.wrappedNormalizedClause
      (Variable := Variable) crossing clause).map
        FormulaShapeDirectionOrdering.literalProfile =
      (FormulaShapeCrossoverDirection.zeroOffsetClause clause).map
        FormulaShapeDirectionOrdering.literalProfile := by
  simp [FormulaShapeCrossoverDirection.wrappedNormalizedClause,
    FormulaShapeCrossoverDirection.zeroOffsetClause,
    FormulaShapeDirectionOrdering.literalProfile,
    List.map_map, Function.comp_def]

/-- Every actual retained halo copy of a crossover clause has the same
finite literal profile as its fixed Figure 8(b) template clause. -/
theorem normalizedClause_crossoverClauseAt_literalProfiles_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossingHalo source.incidenceGraph)
    (clause : EmbeddedClause CrossoverVariable)
    (localClauseIndex : Nat) :
    (normalizedClause source
        ⟨crossoverClauseAt crossing clause,
          .crossover crossing localClauseIndex⟩).map
        FormulaShapeDirectionOrdering.literalProfile =
      (FormulaShapeCrossoverDirection.zeroOffsetClause clause).map
        FormulaShapeDirectionOrdering.literalProfile := by
  rw [normalizedClause_crossoverClauseAt_eq
    source wellFormed degree isLocal crossing crossingMember
    clause localClauseIndex]
  exact wrappedNormalizedClause_literalProfiles_eq
    (Variable := Variable)
    (crossing.periodNormalize source.incidenceGraph) clause

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
