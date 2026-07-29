import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierNoncarrierContacts
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointNoncarrierContacts

/-!
# Endpoint-only contacts for all final route points

Carrier--carrier, carrier--noncarrier, and noncarrier--noncarrier contact
theorems are assembled into the endpoint-contact property required for
periodic ribbon thickening.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Every equality between two distinct witnessed final route-point
occurrences is an outer-endpoint equality. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (different :
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed secondShift)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  by_cases firstCarrier :
      ∃ firstLink,
        first.segmentWitness.routeWitness.metadata.source.component =
          .carrier firstLink
  · rcases firstCarrier with
      ⟨firstLink, firstComponentEq⟩
    by_cases secondCarrier :
        ∃ secondLink,
          second.segmentWitness.routeWitness.metadata.source.component =
            .carrier secondLink
    · rcases secondCarrier with
        ⟨secondLink, secondComponentEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers
          formula wellFormed degree isLocal clausesNonempty
          first second firstLink secondLink
          firstComponentEq secondComponentEq different equal
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier
          formula wellFormed degree isLocal clausesNonempty
          first second firstLink firstComponentEq secondCarrier equal
  · by_cases secondCarrier :
        ∃ secondLink,
          second.segmentWitness.routeWitness.metadata.source.component =
            .carrier secondLink
    · rcases secondCarrier with
        ⟨secondLink, secondComponentEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_noncarrier_carrier
          formula wellFormed degree isLocal clausesNonempty
          first second firstCarrier secondLink secondComponentEq equal
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_noncarriers
          formula wellFormed degree isLocal clausesNonempty
          first second firstCarrier secondCarrier different equal

/-- The complete final periodic drawing has endpoint-only contacts between
all distinct lifted listed route points. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsMeetOnlyAtEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).RoutePointsMeetOnlyAtEndpoints := by
  intro firstIndexed firstMember secondIndexed secondMember
    firstShift secondShift different equal
  rcases
      exists_retainedPhysicalPoint_of_finalRoutePointOccurrence
        formula wellFormed degree isLocal clausesNonempty
        firstIndexed firstMember firstShift with
    ⟨first⟩
  rcases
      exists_retainedPhysicalPoint_of_finalRoutePointOccurrence
        formula wellFormed degree isLocal clausesNonempty
        secondIndexed secondMember secondShift with
    ⟨second⟩
  exact
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints
      formula wellFormed degree isLocal clausesNonempty
      first second different equal

end PeriodicOrthocrossing
end LeanTrominoes
