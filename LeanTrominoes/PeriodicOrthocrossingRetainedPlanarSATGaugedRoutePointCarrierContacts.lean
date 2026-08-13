/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierPerpendicularSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierParallelSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointLocalRouteAvoidance

/-!
# Endpoint-only contacts between final carrier route points

The carrier-pair classification used for continuous planarity already
produces full local-route avoidance for perpendicular carriers, distinct
parallel physical keys, and distinct links on one physical carrier.  Exact
aligned-link equality is the remaining reindexing case.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Final route points carried by perpendicular aligned carrier axes can
coincide only at outer endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers_perpendicular
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
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier firstLink)
    (secondComponentEq :
      second.segmentWitness.routeWitness.metadata.source.component =
        .carrier secondLink)
    (perpendicular :
      CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
          (Cell.sub first.segmentWitness.physicalShift
            second.segmentWitness.physicalShift))
        secondLink)
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
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  have routeAvoid :=
    first.segmentWitness.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_perpendicular
        wellFormed degree isLocal
        second.segmentWitness.routeWitness.metadata
        first.segmentWitness.metadata_retainedValid
        second.segmentWitness.metadata_retainedValid
        reindexShift firstLink secondLink
        firstClauseIndex secondClauseIndex
        firstSourceEq secondSourceEq
        (by simpa only [reindexShift] using perpendicular)
        first.segmentWitness.routeWitness.literalMember
        second.segmentWitness.routeWitness.literalMember
  apply
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_periodTranslate_localRoutesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty first second
  · simpa only [reindexShift] using routeAvoid
  · exact equal

/-- Final route points on distinct aligned parallel carrier keys can
coincide only at outer endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers_parallel_key_ne
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
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier firstLink)
    (secondComponentEq :
      second.segmentWitness.routeWitness.metadata.source.component =
        .carrier secondLink)
    (notPerpendicular :
      ¬CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
          (Cell.sub first.segmentWitness.physicalShift
            second.segmentWitness.physicalShift))
        secondLink)
    (keyDifferent :
      (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
        (Cell.sub first.segmentWitness.physicalShift
          second.segmentWitness.physicalShift)).first.carrierKey ≠
        secondLink.first.carrierKey)
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
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  have routeAvoid :=
    first.segmentWitness.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_parallel_key_ne
        wellFormed degree isLocal
        second.segmentWitness.routeWitness.metadata
        first.segmentWitness.metadata_retainedValid
        second.segmentWitness.metadata_retainedValid
        reindexShift firstLink secondLink
        firstClauseIndex secondClauseIndex
        firstSourceEq secondSourceEq
        (by simpa only [reindexShift] using notPerpendicular)
        (by simpa only [reindexShift] using keyDifferent)
        first.segmentWitness.routeWitness.literalMember
        second.segmentWitness.routeWitness.literalMember
  apply
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_periodTranslate_localRoutesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty first second
  · simpa only [reindexShift] using routeAvoid
  · exact equal

/-- Final route points on one aligned physical carrier can coincide only at
outer endpoints.  Equal aligned links use source reindexing; distinct links
use raw carrier order. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers_same_physical_key
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
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier firstLink)
    (secondComponentEq :
      second.segmentWitness.routeWitness.metadata.source.component =
        .carrier secondLink)
    (samePhysicalKey :
      (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
        (Cell.sub first.segmentWitness.physicalShift
          second.segmentWitness.physicalShift)).first.carrierKey =
        secondLink.first.carrierKey)
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
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  by_cases alignedLinkEq :
      carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink reindexShift =
        secondLink
  · apply
      retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_first_component_aligns_second
        formula wellFormed degree isLocal clausesNonempty
        first second
    · simpa [reindexShift, firstSourceEq, secondSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component,
        alignedLinkEq]
    · exact different
    · exact equal
  · have routeAvoid :=
      first.segmentWitness.routeWitness.metadata
        |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_same_key
          wellFormed degree isLocal
          second.segmentWitness.routeWitness.metadata
          first.segmentWitness.metadata_retainedValid
          second.segmentWitness.metadata_retainedValid
          reindexShift firstLink secondLink
          firstClauseIndex secondClauseIndex
          firstSourceEq secondSourceEq
          (by simpa only [reindexShift] using samePhysicalKey)
          alignedLinkEq
          first.segmentWitness.routeWitness.literalMember
          second.segmentWitness.routeWitness.literalMember
    apply
      retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_periodTranslate_localRoutesAvoidEachOther
        formula wellFormed degree isLocal clausesNonempty first second
    · simpa only [reindexShift] using routeAvoid
    · exact equal

/-- Every contact between distinct final carrier route-point occurrences is
an outer-endpoint contact. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers
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
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier firstLink)
    (secondComponentEq :
      second.segmentWitness.routeWitness.metadata.source.component =
        .carrier secondLink)
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
  let translatedFirstLink :=
    carrierLinkPeriodTranslate formula.incidenceGraph firstLink
      (Cell.sub first.segmentWitness.physicalShift
        second.segmentWitness.physicalShift)
  by_cases perpendicular :
      CarrierLinksPerpendicular translatedFirstLink secondLink
  · exact
      retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers_perpendicular
        formula wellFormed degree isLocal clausesNonempty
        first second firstLink secondLink
        firstComponentEq secondComponentEq
        (by simpa only [translatedFirstLink] using perpendicular)
        equal
  · by_cases samePhysicalKey :
      translatedFirstLink.first.carrierKey =
        secondLink.first.carrierKey
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers_same_physical_key
          formula wellFormed degree isLocal clausesNonempty
          first second firstLink secondLink
          firstComponentEq secondComponentEq
          (by simpa only [translatedFirstLink] using samePhysicalKey)
          different equal
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carriers_parallel_key_ne
          formula wellFormed degree isLocal clausesNonempty
          first second firstLink secondLink
          firstComponentEq secondComponentEq
          (by simpa only [translatedFirstLink] using perpendicular)
          (by simpa only [translatedFirstLink] using samePhysicalKey)
          equal

end PeriodicOrthocrossing
end LeanTrominoes
