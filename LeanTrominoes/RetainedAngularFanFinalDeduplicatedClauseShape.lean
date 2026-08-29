/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedNonempty
import LeanTrominoes.PeriodicCNFPlanarRetainedWidth
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Shape of final duplicate-free clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Source clause nonemptiness passes to every final duplicate-free
normalized clause. -/
theorem deduplicatedClauses_nonempty_of_source
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    ∀ clause ∈ deduplicatedClauses formula,
      clause ≠ [] := by
  rw [← finalCoordinatedSource_erase_clauses_eq]
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty

/-- Source width three passes to every final duplicate-free normalized
clause. -/
theorem deduplicatedClauses_widthAtMostThree
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    ∀ clause ∈ deduplicatedClauses formula,
      clause.length ≤ 3 := by
  rw [← finalCoordinatedSource_erase_clauses_eq]
  exact
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_widthAtMostThree
      formula sourceWidth

end PeriodicEightOccurrenceSplit
end LeanTrominoes
