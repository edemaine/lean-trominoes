/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataLocalRouteLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteLookup

/-! # Raw representative routes of retained-carrier clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Exact normalized-clause and metadata lookups identify a raw
representative route with its local carrier-lens route. -/
theorem rawRepresentativeRoute_eq_carrierClauseMetadataAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex literalIndex : Nat)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? =
        some (normalizedCarrierClauseAt source taggedLink))
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf
            (normalizedCarrierClauseAt source taggedLink)]? =
        some (carrierClauseMetadataAt taggedLink.1 taggedLink.2)) :
    let localClauseIndex := if taggedLink.2 then 0 else 1
    rawRepresentativeRoute source clauseIndex literalIndex =
      (((DrawingPlanarSATClauseSource.carrier
          taggedLink.1 localClauseIndex).incidenceDrawing source).routes
        localClauseIndex literalIndex) := by
  dsimp only
  rw [rawRepresentativeRoute_eq_of_clauseLookup
    source (normalizedCarrierClauseAt source taggedLink)
      clauseIndex literalIndex clauseLookup]
  have routeEq := retainedLocalIncidenceRoute_eq_of_metadataLookup
    source (carrierClauseMetadataAt taggedLink.1 taggedLink.2)
      ((normalizedClauses source).idxOf
        (normalizedCarrierClauseAt source taggedLink))
      literalIndex metadataLookup
  simpa only [carrierClauseMetadataAt,
    DrawingPlanarSATClauseSource.localClauseIndex] using routeEq

/-- Consequently the raw representative has the explicit complete
equality-lens direction word. -/
theorem rawRepresentativeRoute_carrier_directions_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        source.incidenceGraph).product [true, false])
    (clauseIndex literalIndex : Nat)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? =
        some (normalizedCarrierClauseAt source taggedLink))
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf
            (normalizedCarrierClauseAt source taggedLink)]? =
        some (carrierClauseMetadataAt taggedLink.1 taggedLink.2)) :
    let localClauseIndex := if taggedLink.2 then 0 else 1
    Gadget.unitSubdivisionDirections
        (rawRepresentativeRoute source clauseIndex literalIndex) =
      carrierLensRouteDirections taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph taggedLink.1.first)
          (CarrierNode.position source.incidenceGraph taggedLink.1.second))
        localClauseIndex literalIndex := by
  dsimp only
  let localClauseIndex := if taggedLink.2 then 0 else 1
  have linkMember : taggedLink.1 ∈
      retainedDrawingCompleteCarrierLinks source.incidenceGraph :=
    (List.mem_product.mp taggedLinkMember).1
  calc
    Gadget.unitSubdivisionDirections
          (rawRepresentativeRoute source clauseIndex literalIndex) =
        Gadget.unitSubdivisionDirections
          (((DrawingPlanarSATClauseSource.carrier
              taggedLink.1 localClauseIndex).incidenceDrawing source).routes
            localClauseIndex literalIndex) := by
      rw [rawRepresentativeRoute_eq_carrierClauseMetadataAt
        source taggedLink clauseIndex literalIndex
          clauseLookup metadataLookup]
    _ = _ := carrier_routeDirections_eq
      source wellFormed degree isLocal taggedLink.1 linkMember
        localClauseIndex literalIndex

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
