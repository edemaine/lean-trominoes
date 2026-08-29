/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateClausePresentation

/-! # Family presentation of final terminal-coordinate columns -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open TerminalCoordinateComponents

/-- Actual unscaled terminal coordinates of an explicit normalized clause
sublist, retaining its global final-clause indices. -/
def retainedFinalTerminalCoordinatesFrom
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (start : Nat)
    (clauses : List (PeriodicClause Variable)) : List (Nat × Nat) :=
  clauses.zipIdx start |>.flatMap fun taggedClause =>
    taggedClause.1.zipIdx.map fun taggedLiteral =>
      ofLex (retainedOccurrenceTerminalCoordinate routes
        (taggedLiteral.1.atom, taggedClause.2, taggedLiteral.2))

/-- Appending clause families concatenates their actual coordinate columns
and advances the global clause index by the first family's length. -/
theorem retainedFinalTerminalCoordinatesFrom_append
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (start : Nat)
    (first second : List (PeriodicClause Variable)) :
    retainedFinalTerminalCoordinatesFrom routes start (first ++ second) =
      retainedFinalTerminalCoordinatesFrom routes start first ++
        retainedFinalTerminalCoordinatesFrom routes
          (start + first.length) second := by
  unfold retainedFinalTerminalCoordinatesFrom
  rw [List.zipIdx_append, List.flatMap_append]

/-- The actual final unscaled coordinate column is the indexed scan over
the duplicate-free normalized clause presentation. -/
theorem finalCoordinatedTerminalCoordinates_eq_deduplicatedClauses
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    coordinates
        (finalCoordinatedSource formula).erase
        (finalCoordinatedSourceRoutes formula) =
      retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes formula) 0
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses
          formula) := by
  rw [coordinates_eq_clauses,
    finalCoordinatedSource_erase_clauses_eq]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
