import LeanTrominoes.RetainedFinalFlatNormalizedCarrierContacts
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation

/-!
# Final flat routes in the anchor-normalized local drawings

The contact certificates name raw finite components, while the angular-fan
obligation is stated for routes in the final quotient.  Flat routes use
external shift zero, and their recovered physical shift is exactly the
anchor-normalizing translation.  Route equivariance therefore identifies
the final list of points with a route in the normalized local drawing,
without any residual translation.

For carriers the normalized drawing is the lens of `normalizedLink`.  For
noncarriers it is the retained finite source selected by
`FinalGaugedFlatNormalizedMacrocellSource`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A final flat carrier route is literally a route of its raw
anchor-normalized retained equality lens. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.exists_route_eq_normalizedLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    ∃ localClauseIndex,
      taggedRoute.1 =
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrier.normalizedLink).routes
            localClauseIndex
            carrier.coordinates.taggedLiteral.2 := by
  rcases
      carrier.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          carrier.link carrier.componentEq with
    ⟨localClauseIndex, sourceEq⟩
  refine ⟨localClauseIndex, ?_⟩
  rw [carrier.finalRoute_eq_occurrence,
    carrier.routeWitness.routeEq]
  unfold metadataPhysicalRouteOccurrence
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).routeAt
            (metadataPhysicalIncidence
              carrier.routeWitness.metadata
              carrier.routeWitness.metadataIndex
              carrier.routeWitness.literal
              carrier.coordinates.taggedLiteral.2) =
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrier.link).routes
            localClauseIndex
            carrier.coordinates.taggedLiteral.2 := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      carrier.routeWitness.metadataLookup,
      sourceEq,
      DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex]
  rw [localRouteEq]
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  simpa [FinalGaugedFlatCarrierRouteWitness.normalizedLink,
    FinalGaugedRouteOccurrenceWitness.physicalShift] using
      (drawingPlanarSATCarrierLensIncidenceDrawing_routes_periodTranslate
        formula carrier.link
        carrier.routeWitness.physicalShift
        localClauseIndex
        carrier.coordinates.taggedLiteral.2).symm

/-- A final flat noncarrier route is literally the route with the same
local clause and literal indices in its retained anchor-normalized source
drawing. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.routeEq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell) :
    taggedRoute.1 =
      (normalized.source.incidenceDrawing formula).routes
        normalized.source.localClauseIndex
        macrocell.coordinates.taggedLiteral.2 := by
  rw [macrocell.finalRoute_eq_occurrence,
    macrocell.routeWitness.routeEq]
  unfold metadataPhysicalRouteOccurrence
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).routeAt
            (metadataPhysicalIncidence
              macrocell.routeWitness.metadata
              macrocell.routeWitness.metadataIndex
              macrocell.routeWitness.literal
              macrocell.coordinates.taggedLiteral.2) =
        (macrocell.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            macrocell.routeWitness.metadata.source.localClauseIndex
            macrocell.coordinates.taggedLiteral.2 := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      macrocell.routeWitness.metadataLookup]
  rw [localRouteEq]
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  change
    translatePolyline
        (carrierMacroPeriodTranslation formula.incidenceGraph
          macrocell.routeWitness.physicalShift)
        ((macrocell.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            macrocell.routeWitness.metadata.source.localClauseIndex
            macrocell.coordinates.taggedLiteral.2) =
      _
  rw [←
    macrocell.routeWitness.metadata.source
      |>.incidenceDrawing_routes_periodTranslate
        formula macrocell.routeWitness.physicalShift
        macrocell.routeWitness.metadata.source.localClauseIndex
        macrocell.coordinates.taggedLiteral.2]
  have drawingEq :
      normalized.source.incidenceDrawing formula =
        (macrocell.routeWitness.metadata.source.periodTranslate
          formula macrocell.routeWitness.physicalShift
          |>.incidenceDrawing formula) :=
    DrawingPlanarSATClauseSource.incidenceDrawing_eq_of_component_eq
      formula normalized.source
      (macrocell.routeWitness.metadata.source.periodTranslate
        formula macrocell.routeWitness.physicalShift)
      normalized.componentEq
  rw [← drawingEq, ← normalized.localClauseIndexEq]

end PeriodicOrthocrossing
end LeanTrominoes
