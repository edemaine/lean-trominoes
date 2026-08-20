/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingExtensionality
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes

/-! # Exact retained descriptors from finite clause metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Erasing the position-free metadata source recovers exactly its declared
deduplicated normalized clause list. -/
@[simp]
theorem positionedSource_erase_clauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (positionedSource source).erase.clauses =
      deduplicatedClauses source := by
  simp [positionedSource, PositionedPeriodicCNF.erase,
    Function.comp_def]

/-- The finite metadata descriptor stream is exactly the canonical retained
planar descriptor stream used by the hardness pipeline. -/
theorem descriptors_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShapeRetainedPlanarDirection.descriptors source =
      descriptors source := by
  unfold FormulaShapeRetainedPlanarDirection.descriptors descriptors
  apply
    FormulaShapeDirectionOrdering.ofFormula_eq_of_erase_clauses_eq_of_firstDirections_eq
  · rw [positionedSource_erase_clauses_eq,
      positionedSource_erase_clauses]
  · intro clauseIndex literalIndex
    exact
      (incidenceRoutes_firstDirection_eq_representativeRoute
          source clauseIndex literalIndex).trans
        (representativeRoute_firstDirection_eq_rawRepresentativeRoute
          source clauseIndex literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
