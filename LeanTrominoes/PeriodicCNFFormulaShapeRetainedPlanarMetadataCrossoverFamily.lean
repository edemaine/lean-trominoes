/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverBlock
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilyData

/-! # Fixed descriptor stream of the retained crossover family -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The raw fixed-block presentation indexed by every physical neighboring
crossover retained in the finite drawing. -/
def fixedHaloCrossoverClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (orientedCrossingHalo source.incidenceGraph).flatMap fun _ =>
    FormulaShapeCrossoverDirection.descriptors

/-- The exact raw crossover metadata descriptor family is one fixed block
per physical halo crossing. -/
theorem crossoverMetadataClauseDescriptors_eq_fixedHalo
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    crossoverMetadataClauseDescriptors source =
      fixedHaloCrossoverClauseDescriptors source := by
  unfold crossoverMetadataClauseDescriptors
    drawingPlanarSATCrossoverClauseMetadata
    fixedHaloCrossoverClauseDescriptors
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro crossing crossingMember
  exact crossoverMetadataClauseDescriptorsFor_eq
    source wellFormed degree isLocal crossing crossingMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
