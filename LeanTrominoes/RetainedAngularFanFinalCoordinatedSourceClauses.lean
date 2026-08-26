/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionClauses
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDeduplicatedClausesNodup

/-! # Clause presentation of the final coordinated source -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Erasing the positions of the final coordinated clauses gives the final
duplicate-free normalized clause representatives. -/
theorem finalCoordinatedSource_clauseLiterals_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (finalCoordinatedSource formula).clauses.map
        PositionedPeriodicClause.literals =
      deduplicatedClauses formula := by
  change
    (PeriodicCNF.FormulaShapeRetainedPlanarDirection.positionedSource
        formula).clauses.map PositionedPeriodicClause.literals = _
  simpa [PositionedPeriodicCNF.erase] using
    positionedSource_erase_clauses_eq formula

/-- Final coordinated clauses have pairwise-distinct literal lists. -/
theorem finalCoordinatedSource_clauseLiterals_nodup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((finalCoordinatedSource formula).clauses.map
      PositionedPeriodicClause.literals).Nodup := by
  rw [finalCoordinatedSource_clauseLiterals_eq]
  exact deduplicatedClauses_nodup formula

end PeriodicEightOccurrenceSplit
end LeanTrominoes
