/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteSimplicity
import LeanTrominoes.PeriodicGridDrawingIndexedSegmentLookup
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-!
# Separation within one final retained route occurrence

Route simplicity handles all contacts between different indexed segments
belonging to the same stored route at the same periodic translate.  This
module states that consequence directly in the global periodic drawing
language, for both continuous interior overlap and the asymmetric
interior-versus-closed contact used by `RoutesAvoidInteriors`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Distinct segments of one final stored route have disjoint interiors
after any common periodic translation. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_sameRouteOccurrence_interiorsDisjoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : IndexedGridSegment}
    (firstMember :
      first ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (secondMember :
      second ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (sameRoute : first.routeIndex = second.routeIndex)
    (differentSegment :
      first.segmentIndex ≠ second.segmentIndex)
    (shift : Cell) :
    ¬GridSegment.InteriorsMeet
      (first.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift))
      (second.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift)) := by
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  rcases
      PeriodicGridDrawing.exists_commonRoute_of_mem_indexedSegments_of_routeIndex_eq
        firstMember secondMember sameRoute with
    ⟨route, routeMember, firstSegmentMember,
      secondSegmentMember⟩
  have simple :
      LocalIncidenceDrawing.RouteIsSimple route :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      route (List.fst_mem_of_mem_zipIdx routeMember)
  intro meet
  apply
    simple.2.2
      (first.segment, first.segmentIndex)
      firstSegmentMember
      (second.segment, second.segmentIndex)
      secondSegmentMember
      differentSegment
  exact
    (GridSegment.interiorsMeet_translate_both_iff
      first.segment second.segment
      (drawing.periodTranslation shift)).mp
      (by simpa only [drawing] using meet)

/-- Within one final route occurrence, the interior of one segment cannot
meet the closed extent of a different segment. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_sameRouteOccurrence_avoidsInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : IndexedGridSegment}
    (firstMember :
      first ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (secondMember :
      second ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (sameRoute : first.routeIndex = second.routeIndex)
    (differentSegment :
      first.segmentIndex ≠ second.segmentIndex)
    (shift point : Cell)
    (firstContains :
      (first.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift)).InteriorContains point) :
    ¬(second.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift)).Contains point := by
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  rcases
      PeriodicGridDrawing.exists_commonRoute_of_mem_indexedSegments_of_routeIndex_eq
        firstMember secondMember sameRoute with
    ⟨route, routeMember, firstSegmentMember,
      secondSegmentMember⟩
  have simple :
      LocalIncidenceDrawing.RouteIsSimple route :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      route (List.fst_mem_of_mem_zipIdx routeMember)
  let normalized := drawing.normalizePoint point shift
  have normalizedFirst :
      first.segment.InteriorContains normalized := by
    apply
      (PeriodicGridDrawing.interiorContains_translate_iff
        first.segment (drawing.periodTranslation shift)
        normalized).mp
    rw [drawing.normalizePoint_add point shift]
    simpa only [drawing] using firstContains
  intro secondContains
  have normalizedSecond :
      second.segment.Contains normalized := by
    apply
      (PeriodicGridDrawing.contains_translate_iff
        second.segment (drawing.periodTranslation shift)
        normalized).mp
    rw [drawing.normalizePoint_add point shift]
    simpa only [drawing] using secondContains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        normalizedSecond with
    secondInterior | secondEndpoint
  · exact
      (simple.2.2
        (first.segment, first.segmentIndex)
        firstSegmentMember
        (second.segment, second.segmentIndex)
        secondSegmentMember
        differentSegment)
        (GridSegment.interiorsMeet_of_interiorContains
          normalizedFirst secondInterior)
  · have endpointMember :
        normalized ∈ route := by
      have endpoints :=
        gridPolylineSegments_endpoints_mem
          (List.fst_mem_of_mem_zipIdx secondSegmentMember)
      rcases secondEndpoint with atStart | atFinish
      · exact atStart.symm ▸ endpoints.1
      · exact atFinish.symm ▸ endpoints.2
    exact
      (simple.2.1 normalized endpointMember
        first.segment
        (List.fst_mem_of_mem_zipIdx firstSegmentMember))
        normalizedFirst

end PeriodicOrthocrossing
end LeanTrominoes
