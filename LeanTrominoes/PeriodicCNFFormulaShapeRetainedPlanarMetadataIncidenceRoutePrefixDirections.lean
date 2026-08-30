/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutePrefixDirections
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes

/-! # Prefix directions of final retained incidence routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Gadget
open PeriodicOrthocrossing

/-- Final clause deduplication and outer anchor normalization preserve the
representative prefix direction word. -/
theorem incidenceRoutes_prefixDirections_eq_representativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex).dropLast =
      unitSubdivisionDirections
        (representativeRoute source clauseIndex literalIndex).dropLast := by
  let normalizedSource :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source
  let normalizedRoutes :=
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source
  change
    unitSubdivisionDirections
        (normalizedSource.deduplicatedIncidenceRoutes
          placement normalizedRoutes clauseIndex literalIndex).dropLast = _
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
      rw [PositionedPeriodicCNF.unitSubdivisionDirections_normalizeIncidenceRoute_dropLast]
      unfold representativeRoute
      rw [metadataLookup]
      rw [representativeClauseIndex_eq source clause.literals]

/-- Hence every final retained route has exactly the raw metadata-route
prefix direction word selected by its stable representative. -/
theorem incidenceRoutes_prefixDirections_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex).dropLast =
      unitSubdivisionDirections
        (rawRepresentativeRoute source clauseIndex literalIndex).dropLast :=
  (incidenceRoutes_prefixDirections_eq_representativeRoute
    source clauseIndex literalIndex).trans
      (representativeRoute_prefixDirections_eq_rawRepresentativeRoute
        source clauseIndex literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
