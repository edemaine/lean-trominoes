/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineMiddleCoarsening
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionData
import LeanTrominoes.RetainedAngularFanSourceOwnCycleSeparation
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-! # Source-prefix/fan-suffix decomposition of fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- The source part retained after deleting the old variable endpoint. -/
def retainedFallbackSourcePrefix (route : List Cell) : List Cell :=
  (scalePolyline retainedTerminalFanTotalRefinement route).dropLast

/-- Center of the retained fan attached to the deleted endpoint. -/
def retainedFallbackFanCenter (route : List Cell) : Cell :=
  Cell.scale retainedTerminalFanTotalRefinement
    (route.getLastD (0, 0))

/-- Uniform view of the existing ordinary and delayed-lane complete routes. -/
def RetainedFallbackFanKind.splicedOwnFigure7Route
    (kind : RetainedFallbackFanKind)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  match kind with
  | .ordinary =>
      retainedAngularFanSplicedOwnFigure7Route
        route terminal slot (route.getLastD (0, 0))
  | .escaped =>
      retainedAngularFanEscapedSplicedOwnFigure7Route
        route terminal slot (route.getLastD (0, 0))

private theorem ordinaryOuterRoute_ne_nil
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterCompleteRoute center terminal slot ≠ [] := by
  intro empty
  have head := retainedTerminalFanOuterCompleteRoute_head?
    center terminal slot
  rw [empty] at head
  simp at head

private theorem escapedOuterRoute_ne_nil
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot ≠ [] := by
  intro empty
  have head := retainedTerminalFanOuterEscapedCompleteRoute_head?
    center terminal slot
  rw [empty] at head
  simp at head

/-- After rasterizing the orthogonal tail replacement, both fallback
policies are literally the source prefix joined to the translation-free fan
suffix named in `RetainedAngularFanFallbackSuffixDirectionData`. -/
theorem RetainedFallbackFanKind.splicedOwnFigure7Route_eq_join
    (kind : RetainedFallbackFanKind)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal : OrthogonalPolyline route)
    (valid : kind.Valid terminal) :
    kind.splicedOwnFigure7Route route terminal slot =
      joinAtEndpoint
        (retainedFallbackSourcePrefix route)
        (retainedFallbackFanSuffixRouteAt
          kind (retainedFallbackFanCenter route) terminal slot) := by
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  have prefixLast :
      sourcePrefix.getLast? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    simpa [sourcePrefix, retainedFallbackSourcePrefix,
      center, retainedFallbackFanCenter, scaledRoute] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route terminal slot routeLength classified
  cases kind with
  | ordinary =>
      let outer :=
        retainedTerminalFanOuterCompleteRoute center terminal slot
      let spoke :=
        retainedTerminalFanFigure7SpokeRouteAt center slot
      have outerHead :
          outer.head? =
            some
              (retainedAngularFanOuterDemand
                center terminal slot).gate := by
        exact retainedTerminalFanOuterCompleteRoute_head?
          center terminal slot
      have boundaryOrthogonal :
          OrthogonalPolyline
            (retainedAngularFanSplicedBoundaryPolyline
              route terminal slot) :=
        retainedAngularFanSplicedBoundaryPolyline_orthogonal
          route terminal slot routeLength classified routeOrthogonal
      have boundaryEq :
          retainedAngularFanSplicedBoundaryRoute route terminal slot =
            joinAtEndpoint sourcePrefix outer := by
        unfold retainedAngularFanSplicedBoundaryRoute
        rw [rasterizeRetainedPolyline_eq_of_orthogonal
          boundaryOrthogonal]
        unfold retainedAngularFanSplicedBoundaryPolyline
        exact replacePolylineTail_eq_joinAtEndpoint_dropLast
          scaledRoute outer prefixLast outerHead
      change
        joinAtEndpoint
            (retainedAngularFanSplicedBoundaryRoute
              route terminal slot)
            spoke =
          joinAtEndpoint sourcePrefix
            (joinAtEndpoint outer spoke)
      rw [boundaryEq]
      exact (joinAtEndpoint_assoc_of_middle_ne_nil
        (ordinaryOuterRoute_ne_nil center terminal slot)).symm
  | escaped =>
      let outer :=
        retainedTerminalFanOuterEscapedCompleteRoute center terminal slot
      let spoke :=
        retainedTerminalFanFigure7SpokeRouteAt center slot
      have outerHead :
          outer.head? =
            some
              (retainedAngularFanOuterDemand
                center terminal slot).gate := by
        exact retainedTerminalFanOuterEscapedCompleteRoute_head?
          center terminal slot
      have boundaryOrthogonal :
          OrthogonalPolyline
            (retainedAngularFanEscapedSplicedBoundaryPolyline
              route terminal slot) :=
        retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
          route terminal slot routeLength classified routeOrthogonal valid
      have boundaryEq :
          retainedAngularFanEscapedSplicedBoundaryRoute
              route terminal slot =
            joinAtEndpoint sourcePrefix outer := by
        unfold retainedAngularFanEscapedSplicedBoundaryRoute
        rw [rasterizeRetainedPolyline_eq_of_orthogonal
          boundaryOrthogonal]
        unfold retainedAngularFanEscapedSplicedBoundaryPolyline
        exact replacePolylineTail_eq_joinAtEndpoint_dropLast
          scaledRoute outer prefixLast outerHead
      change
        joinAtEndpoint
            (retainedAngularFanEscapedSplicedBoundaryRoute
              route terminal slot)
            spoke =
          joinAtEndpoint sourcePrefix
            (joinAtEndpoint outer spoke)
      rw [boundaryEq]
      exact (joinAtEndpoint_assoc_of_middle_ne_nil
        (escapedOuterRoute_ne_nil center terminal slot)).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
