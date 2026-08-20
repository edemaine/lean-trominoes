/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionClauses
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteData
import LeanTrominoes.PositionedPeriodicCNFRouteFirstDirections

/-! # Final retained first directions from representative metadata routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Looking up a final positioned clause and forgetting its position is the
same lookup in the deduplicated normalized metadata clause list. -/
theorem positionedSource_clauseLiterals?_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    ((FormulaShapeRetainedPlanarDirection.positionedSource
        source).clauses[clauseIndex]?).map
          PositionedPeriodicClause.literals =
      (deduplicatedClauses source)[clauseIndex]? := by
  have clausesEq := positionedSource_erase_clauses_eq source
  have lookupEq := congrArg (fun clauses => clauses[clauseIndex]?) clausesEq
  simpa [PositionedPeriodicCNF.erase] using lookupEq

/-- The source representative index selected by positioned deduplication is
exactly `idxOf` in the normalized metadata clause list. -/
theorem representativeClauseIndex_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause : PeriodicClause
      (WrappedPeriodicPlanarSATVariable Variable)) :
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source).representativeClauseIndex clause =
      (normalizedClauses source).idxOf clause := by
  unfold PositionedPeriodicCNF.representativeClauseIndex
  rw [anchorNormalized_erase_clauses_eq]

/-- Final clause deduplication and its outer anchor normalization do not add
any first-direction information: the direction is exactly that of the first
normalized source route carrying the retained literal list. -/
theorem incidenceRoutes_firstDirection_eq_representativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (representativeRoute source clauseIndex literalIndex) := by
  let normalizedSource :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source
  let normalizedRoutes :=
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source
  change
    AxisDirection.polylineFirstDirection
        (normalizedSource.deduplicatedIncidenceRoutes
          placement normalizedRoutes clauseIndex literalIndex) = _
  unfold PositionedPeriodicCNF.deduplicatedIncidenceRoutes
  generalize clauseLookup :
      normalizedSource.deduplicateByLiterals.clauses[clauseIndex]? =
        clauseOption
  cases clauseOption with
  | none =>
      have metadataLookup :
          (deduplicatedClauses source)[clauseIndex]? = none := by
        have lookup := positionedSource_clauseLiterals?_eq source clauseIndex
        change
          (normalizedSource.deduplicateByLiterals.clauses[clauseIndex]?).map
              PositionedPeriodicClause.literals = _
          at lookup
        rw [clauseLookup] at lookup
        exact lookup.symm
      simp [representativeRoute, metadataLookup]
  | some clause =>
      have metadataLookup :
          (deduplicatedClauses source)[clauseIndex]? =
            some clause.literals := by
        have lookup := positionedSource_clauseLiterals?_eq source clauseIndex
        change
          (normalizedSource.deduplicateByLiterals.clauses[clauseIndex]?).map
              PositionedPeriodicClause.literals = _
          at lookup
        rw [clauseLookup] at lookup
        exact lookup.symm
      rw [PositionedPeriodicCNF.polylineFirstDirection_normalizeIncidenceRoute]
      unfold representativeRoute
      rw [metadataLookup]
      rw [representativeClauseIndex_eq source clause.literals]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
