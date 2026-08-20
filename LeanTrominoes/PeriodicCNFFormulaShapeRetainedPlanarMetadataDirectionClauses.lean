/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData

/-! # Exact retained planar clauses from finite metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Before clause-orbit deduplication, erasing positions gives exactly the
normalized retained metadata clauses. -/
theorem anchorNormalized_erase_clauses_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source).erase.clauses = normalizedClauses source := by
  unfold
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedDrawingPositionedPeriodicPlanarSATFormula
    positionPeriodicizedPlanarSATFormula
    PositionedPeriodicCNF.anchorNormalize
    PositionedPeriodicCNF.variableGauge
    PositionedPeriodicCNF.rename
    PositionedPeriodicCNF.erase
    normalizedClauses normalizedClause
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
  simp only [List.map_map, Function.comp_def, wrapPeriodicPlanarSATClause]
  apply List.map_congr_left
  intro metadata _metadataMember
  congr 2

/-- The erased clause list of the final retained source is the ordinary
deduplication of the normalized metadata clause list. -/
theorem positionedSource_erase_clauses_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (FormulaShapeRetainedPlanarDirection.positionedSource
      source).erase.clauses = deduplicatedClauses source := by
  rw [show FormulaShapeRetainedPlanarDirection.positionedSource source =
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source).deduplicateByLiterals by rfl]
  rw [PositionedPeriodicCNF.erase_deduplicateByLiterals]
  unfold PeriodicCNF.deduplicate deduplicatedClauses
  rw [anchorNormalized_erase_clauses_eq]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
