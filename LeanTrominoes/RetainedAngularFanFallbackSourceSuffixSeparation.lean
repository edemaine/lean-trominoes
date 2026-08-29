/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineSimpleFinalSegmentSeparation
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections
import LeanTrominoes.RetainedAngularFanFinalSourceHeadSeparationSupport
import LeanTrominoes.RetainedAngularFanOuterEscapedSourceSeparation
import LeanTrominoes.RetainedAngularFanOuterSourceSeparation

/-! # Separating a fallback source prefix from its fan suffix

The leading part of a simple retained source route is separated from the
radius-288 neighborhood of its discarded final segment.  Both fallback
policies and the common Figure 7 spoke stay inside that neighborhood.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every point of either complete fallback suffix stays in the radius-288
expansion of the refined discarded-final-segment rectangle. -/
theorem retainedFallbackFanSuffixRouteAt_point_in_finalSegmentRectangle
    {factor : Nat}
    (kind : RetainedFallbackFanKind)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (valid : kind.Valid
      (scaleRetainedTerminalData factor terminal))
    {point : Cell}
    (pointMember :
      point ∈ retainedFallbackFanSuffixRouteAt
        kind
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal) slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ : GridSegment).coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ : GridSegment).coordinateUpper))
      point := by
  unfold retainedFallbackFanSuffixRouteAt at pointMember
  rcases mem_joinAtEndpoint pointMember with
    outerMember | spokeMember
  · cases kind with
    | ordinary =>
        exact
          retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
            (factor := factor) route terminal slot routeLength classified
            outerMember
    | escaped =>
        have escapeFits :
            retainedTerminalFanOuterSourceEscapeLength ≤
              retainedTerminalFanOuterRadialLength
                (scaleRetainedTerminalData factor terminal) := by
          simpa [RetainedFallbackFanKind.Valid] using valid
        exact
          retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
            (factor := factor) route terminal slot routeLength classified
            escapeFits outerMember
  · let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
    have refinementNonnegative :
        (0 : Int) ≤ retainedTerminalFanTotalRefinement * factor := by
      exact_mod_cast Nat.zero_le
        (retainedTerminalFanTotalRefinement * factor)
    have centerBounded :
        InClosedGridRectangle
          (Cell.scale (retainedTerminalFanTotalRefinement * factor)
            finalSegment.coordinateLower)
          (Cell.scale (retainedTerminalFanTotalRefinement * factor)
            finalSegment.coordinateUpper)
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0))) := by
      have scaled :=
        finalSegment.finish_in_coordinateRectangle.scale
          refinementNonnegative
      rw [scalePolyline_getLastD, Cell.scale_scale]
      simpa [finalSegment, Nat.cast_mul] using scaled
    have spokeBounded :
        WithinCoordinateRadius 96
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0))) point :=
      retainedTerminalFanFigure7SpokeRouteAt_point_within
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor route).getLastD (0, 0)))
        slot point spokeMember
    exact
      inClosedGridRectangle_coordinateRadius_mono
        (inClosedGridRectangle_coordinateRadius_of_center
          centerBounded spokeBounded)
        (by omega)

/-- Removing the source-prefix gate leaves a prefix strictly separated from
the complete fallback suffix of either policy. -/
theorem retainedFallbackSourcePrefix_dropLast_strictlyAvoids_suffix
    {factor : Nat}
    (kind : RetainedFallbackFanKind)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (factorPositive : 0 < factor)
    (clearance :
      288 < retainedTerminalFanTotalRefinement * factor)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (orthogonal : OrthogonalPolyline route)
    (valid : kind.Valid
      (scaleRetainedTerminalData factor terminal)) :
    RoutesStrictlyAvoidEachOther
      (retainedFallbackSourcePrefix
        (scalePolyline factor route)).dropLast
      (retainedFallbackFanSuffixRouteAt
        kind
          (retainedFallbackFanCenter (scalePolyline factor route))
          (scaleRetainedTerminalData factor terminal) slot) := by
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
  have routeNonempty : route ≠ [] := by
    intro routeEmpty
    rw [routeEmpty] at routeLength
    simp at routeLength
  let finalPoint := route.getLast routeNonempty
  have finalLookup : route.getLast? = some finalPoint :=
    List.getLast?_eq_some_getLast routeNonempty
  have finalD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, finalLookup]
    rfl
  have reverseTailExists :
      ∃ entrance, route.reverse.tail.head? = some entrance :=
    exists_reverse_tail_head?_of_two_le_length route routeLength
  have entranceLookup :
      route.dropLast.getLast? = some (polylineLastEntrance route) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have sourceAvoids :
      RoutesStrictlyAvoidEachOther
        route.dropLast.dropLast
        [finalSegment.start, finalSegment.finish] := by
    change RoutesStrictlyAvoidEachOther route.dropLast.dropLast
      [polylineLastEntrance route, route.getLastD (0, 0)]
    rw [finalD]
    exact
      routeIsSimple_dropLast_dropLast_strictlyAvoids_finalSegment
        simple entranceLookup finalLookup
  have finalAligned : finalSegment.IsAxisAligned := by
    exact (orthogonalPolyline_iff_segments route).mp orthogonal
      finalSegment (by
        simpa [finalSegment] using finalGridSegment_mem route routeLength)
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_axisAlignedSegmentNeighborhood
      (source := route.dropLast.dropLast)
      (nearby := retainedFallbackFanSuffixRouteAt
        kind
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal) slot)
      (reference := finalSegment)
      (factor := retainedTerminalFanTotalRefinement * factor)
      (radius := 288)
      (Nat.mul_pos (by native_decide) factorPositive) clearance
      finalAligned sourceAvoids
      (fun point pointMember => by
        simpa [finalSegment] using
          retainedFallbackFanSuffixRouteAt_point_in_finalSegmentRectangle
            (factor := factor) kind route terminal slot routeLength
            classified valid pointMember)
  change RoutesStrictlyAvoidEachOther
    ((scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline factor route)).dropLast.dropLast)
    (retainedFallbackFanSuffixRouteAt kind
      (Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor route).getLastD (0, 0)))
      (scaleRetainedTerminalData factor terminal) slot)
  rw [scalePolyline_scalePolyline_nat]
  rw [← Nat.cast_mul]
  rw [scalePolyline_dropLast_eq, scalePolyline_dropLast_eq]
  exact separated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
