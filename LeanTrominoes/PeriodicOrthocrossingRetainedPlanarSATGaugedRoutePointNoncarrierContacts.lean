/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierContacts

/-!
# Endpoint-only contacts between final noncarrier route points

The translated macrocell-center classification from continuous planarity
is reused without loss.  Different centers give strict local-route
avoidance; equal centers either identify the translated components, or
expose the routed-variable distinct-arm exception, whose local drawings
also avoid one another.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Every contact between distinct final noncarrier route-point
occurrences is an outer-endpoint contact. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_noncarriers
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
    (firstNotCarrier :
      ¬∃ link,
        first.segmentWitness.routeWitness.metadata.source.component =
          .carrier link)
    (secondNotCarrier :
      ¬∃ link,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier link)
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
  let reindexShift :=
    Cell.sub first.segmentWitness.physicalShift
      second.segmentWitness.physicalShift
  rcases
      first.segmentWitness.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula firstNotCarrier with
    ⟨firstCenter, firstCenterEq⟩
  rcases
      second.segmentWitness.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula secondNotCarrier with
    ⟨secondCenter, secondCenterEq⟩
  by_cases centersEqual :
      Cell.add firstCenter
          ((drawing formula.incidenceGraph).periodTranslation
            reindexShift) =
        secondCenter
  · have firstTranslatedCenterEq :
        ((first.segmentWitness.routeWitness.metadata.source.periodTranslate
            formula reindexShift).component
          |>.macrocellCenter formula) =
          some secondCenter := by
      rw [DrawingPlanarSATClauseSource.component_periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter_periodTranslate,
        firstCenterEq]
      exact congrArg some centersEqual
    have classification :=
      retainedNoncarrierComponents_periodTranslate_eq_or_routedVariable_of_center_eq
        formula wellFormed degree isLocal
        first.segmentWitness.routeWitness.metadata
        second.segmentWitness.routeWitness.metadata
        first.segmentWitness.metadata_retainedValid
        second.segmentWitness.metadata_retainedValid
        reindexShift secondCenter
        firstTranslatedCenterEq secondCenterEq
    rcases classification with componentAlignment | exception
    · apply
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_first_component_aligns_second
          formula wellFormed degree isLocal clausesNonempty
          first second
      · simpa only [reindexShift] using componentAlignment
      · exact different
      · exact equal
    · rcases exception with
        ⟨site, firstArm, firstLink, secondArm, secondLink,
          firstComponentEq, secondComponentEq⟩
      by_cases armsEqual : firstArm = secondArm
      · subst secondArm
        have componentAlignment :=
          first.segmentWitness.routeWitness.metadata
            |>.periodTranslate_component_eq_of_routedVariable_same_arm
              wellFormed degree
              second.segmentWitness.routeWitness.metadata
              first.segmentWitness.metadata_retainedValid
              second.segmentWitness.metadata_retainedValid
              reindexShift site firstArm firstLink secondLink
              firstComponentEq secondComponentEq
        apply
          retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_first_component_aligns_second
            formula wellFormed degree isLocal clausesNonempty
            first second
        · simpa only [reindexShift] using componentAlignment
        · exact different
        · exact equal
      · have routeAvoid :=
          first.segmentWitness.routeWitness.metadata
            |>.periodTranslate_localRoutes_avoidEachOther_of_routedVariable_arms_ne
              second.segmentWitness.routeWitness.metadata
              first.segmentWitness.metadata_retainedValid
              second.segmentWitness.metadata_retainedValid
              reindexShift site firstArm secondArm firstLink secondLink
              firstComponentEq secondComponentEq armsEqual
              first.segmentWitness.routeWitness.literalMember
              second.segmentWitness.routeWitness.literalMember
        apply
          retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_periodTranslate_localRoutesAvoidEachOther
            formula wellFormed degree isLocal clausesNonempty
            first second
        · simpa only [reindexShift] using routeAvoid
        · exact equal
  · have routeAvoid :=
      first.segmentWitness.routeWitness.metadata
        |>.periodTranslate_localRoutes_avoidEachOther_of_macrocellCenters_ne
          wellFormed degree isLocal
          second.segmentWitness.routeWitness.metadata
          first.segmentWitness.metadata_retainedValid
          second.segmentWitness.metadata_retainedValid
          firstCenter secondCenter reindexShift
          firstCenterEq secondCenterEq
          first.segmentWitness.routeWitness.literalMember
          second.segmentWitness.routeWitness.literalMember
          centersEqual
    apply
      retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_periodTranslate_localRoutesAvoidEachOther
        formula wellFormed degree isLocal clausesNonempty
        first second
    · simpa only [reindexShift] using routeAvoid
    · exact equal

end PeriodicOrthocrossing
end LeanTrominoes
