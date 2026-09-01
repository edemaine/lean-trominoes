/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackPrefixDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataLocalRouteLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendClauseDescriptorLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteLookup

/-! # Raw representative routes of retained-bend clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Exact normalized-clause and metadata lookups identify a raw
representative route with its local bend-corner route. -/
theorem rawRepresentativeRoute_eq_bendClauseMetadataAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (selectedBend : RouteBend)
    (clauseIndex literalIndex : Nat)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? =
        some (normalizedBendClauseAt source taggedBend))
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf
            (normalizedBendClauseAt source taggedBend)]? =
        some (bendClauseMetadataAt source.incidenceGraph
          selectedBend taggedBend.2)) :
    rawRepresentativeRoute source clauseIndex literalIndex =
      (((DrawingPlanarSATClauseSource.bend selectedBend
          (if taggedBend.2 then 0 else 1)).incidenceDrawing source).routes
        (if taggedBend.2 then 0 else 1) literalIndex) := by
  rw [rawRepresentativeRoute_eq_of_clauseLookup
    source (normalizedBendClauseAt source taggedBend)
      clauseIndex literalIndex clauseLookup]
  have routeEq := retainedLocalIncidenceRoute_eq_of_metadataLookup
    source
      (bendClauseMetadataAt source.incidenceGraph
        selectedBend taggedBend.2)
      ((normalizedClauses source).idxOf
        (normalizedBendClauseAt source taggedBend))
      literalIndex metadataLookup
  simpa only [bendClauseMetadataAt,
    DrawingPlanarSATClauseSource.localClauseIndex] using routeEq

/-- Consequently, deleting the variable endpoint exposes the selected
corner-table prefix word. -/
theorem rawRepresentativeRoute_bend_prefixDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (selectedBend : RouteBend)
    (clauseIndex literalIndex : Nat)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? =
        some (normalizedBendClauseAt source taggedBend))
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf
            (normalizedBendClauseAt source taggedBend)]? =
        some (bendClauseMetadataAt source.incidenceGraph
          selectedBend taggedBend.2)) :
    Gadget.unitSubdivisionDirections
        (rawRepresentativeRoute source clauseIndex literalIndex).dropLast =
      bendRoutePrefixDirections selectedBend.incomingPort
        selectedBend.outgoingPort
        (if taggedBend.2 then 0 else 1) literalIndex := by
  rw [rawRepresentativeRoute_eq_bendClauseMetadataAt source taggedBend
    selectedBend clauseIndex literalIndex clauseLookup metadataLookup]
  exact bend_routePrefixDirections_eq source selectedBend
    (if taggedBend.2 then 0 else 1) literalIndex

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
