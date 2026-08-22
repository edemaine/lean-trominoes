/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilyData

/-! # Per-bend clause-descriptor blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The two local clause descriptors contributed by one routed bend. -/
def bendClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATBendClauseMetadataFor
      (Variable := Variable) source.incidenceGraph routeBend).map
    (metadataClauseDescriptor source)

@[simp] theorem bendClauseDescriptors_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    (bendClauseDescriptors source routeBend).length = 2 := by
  simp [bendClauseDescriptors,
    drawingPlanarSATBendClauseMetadataFor,
    drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt, equalityInstance]

/-- The complete retained bend descriptor family is the presentation-order
concatenation of the two-token block of each deduplicated routed bend. -/
theorem bendMetadataClauseDescriptors_eq_flatMap_bendBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    bendMetadataClauseDescriptors source =
      (drawingRouteBends source.incidenceGraph).dedup.flatMap
        (bendClauseDescriptors source) := by
  unfold bendMetadataClauseDescriptors drawingPlanarSATBendClauseMetadata
  rw [List.map_flatMap]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
