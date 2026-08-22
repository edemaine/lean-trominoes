/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverDescriptor

/-! # Fixed descriptor block at one retained crossover -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Mapping local metadata descriptors over one physical crossover gadget
produces the fixed twenty-six-token Figure 8(b) block. -/
theorem crossoverMetadataClauseDescriptorsFor_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossingHalo source.incidenceGraph) :
    (drawingPlanarSATCrossoverClauseMetadataFor
        (Variable := Variable) crossing).map
        (metadataClauseDescriptor source) =
      FormulaShapeCrossoverDirection.descriptors := by
  unfold drawingPlanarSATCrossoverClauseMetadataFor
    drawingPlanarSATCrossoverFormulaAt
    scopedCrossoverInstance instantiateFormula
    FormulaShapeCrossoverDirection.descriptors
  simp only [List.map_map, List.zipIdx_map]
  apply List.map_congr_left
  intro taggedClause _taggedClauseMember
  exact metadataClauseDescriptor_crossoverClauseAt_eq
    source wellFormed degree isLocal crossing crossingMember
    taggedClause.1 taggedClause.2

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
