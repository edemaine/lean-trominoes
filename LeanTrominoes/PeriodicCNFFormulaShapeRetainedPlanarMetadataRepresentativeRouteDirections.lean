/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteDirections
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes

/-! # Complete directions of final retained representative routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Gadget
open PeriodicOrthocrossing

/-- Final clause deduplication and its outer anchor normalization preserve
the complete direction word of the selected representative route. -/
theorem incidenceRoutes_directions_eq_representativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex) =
      unitSubdivisionDirections
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
    unitSubdivisionDirections
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
      rw [PositionedPeriodicCNF.unitSubdivisionDirections_normalizeIncidenceRoute]
      unfold representativeRoute
      rw [metadataLookup]
      rw [representativeClauseIndex_eq source clause.literals]

/-- Hence every final retained planar route has exactly the complete raw
metadata-route direction word selected by its stable representative. -/
theorem incidenceRoutes_directions_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex) =
      unitSubdivisionDirections
        (rawRepresentativeRoute source clauseIndex literalIndex) :=
  (incidenceRoutes_directions_eq_representativeRoute
    source clauseIndex literalIndex).trans
      (representativeRoute_directions_eq_rawRepresentativeRoute
        source clauseIndex literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
