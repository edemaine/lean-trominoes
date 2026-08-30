/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardCancellationTarget
import LeanTrominoes.RetainedAngularFanFallbackRouteSimplicity

/-! # Bounded forward-cardinal cancellation after source scaling -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- At the public source-scaling interface, bounded cancellation produces
the same source `take` and normalized-suffix `drop` word used by geometric
normalization. -/
theorem boundedCancellation_scaledForwardCardinalFallback
    {factor : Nat}
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (port : Port)
    (scaledLength distance : Nat)
    (factorPositive : 0 < factor)
    (clearance :
      288 < retainedTerminalFanTotalRefinement * factor)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeSimple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeOrthogonal : OrthogonalPolyline route)
    (scaledTerminalEq :
      scaleRetainedTerminalData factor terminal =
        (.compass port, scaledLength))
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (scaledLengthLarge : 2 ≤ scaledLength)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix
        (scalePolyline factor route)).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter
                (scalePolyline factor route))
              (.compass port, scaledLength) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    let sourceWord :=
      Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix
          (scalePolyline factor route))
    let fanWord :=
      retainedNormalizedFallbackFanSuffixDirections
        .ordinary (scaleRetainedTerminalData factor terminal) slot
    let trim := retainedTerminalFanOuterLaneSpacing * slot.val
    BoundedDelimitedDirectionCancellation.output
        (DelimitedRouteJoin.delimited (sourceWord ++ fanWord)) =
      DelimitedRouteJoin.delimited
        (sourceWord.take (sourceWord.length - trim) ++
          fanWord.drop trim) := by
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let sourceWord := Gadget.unitSubdivisionDirections
    (retainedFallbackSourcePrefix scaledRoute)
  let fanWord := retainedNormalizedFallbackFanSuffixDirections
    .ordinary scaledTerminal slot
  let trim := retainedTerminalFanOuterLaneSpacing * slot.val
  let center := retainedFallbackFanCenter scaledRoute
  have routeLengthTwo : 2 ≤ route.length := by omega
  have scaledRouteLengthThree : 3 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified factorPositive classified
  have scaledTerminalEq' :
      scaledTerminal = (.compass port, scaledLength) := by
    simpa [scaledTerminal] using scaledTerminalEq
  have scaledClassifiedPort :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some (.compass port, scaledLength) := by
    rw [scaledClassified, scaledTerminalEq']
  have scaledSimple : LocalIncidenceDrawing.RouteIsSimple scaledRoute :=
    routeIsSimple_scalePolyline
      (by exact_mod_cast factorPositive) routeSimple
  have scaledOrthogonal : OrthogonalPolyline scaledRoute :=
    routeOrthogonal.scalePolyline
      (by exact_mod_cast factorPositive)
  have sourcePrefixSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (retainedFallbackSourcePrefix scaledRoute) :=
    retainedFallbackSourcePrefix_isSimple scaledRoute scaledSimple
  have sourceStrict :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        (retainedFallbackSourcePrefix scaledRoute).dropLast
        (retainedFallbackFanSuffixRouteAt
          .ordinary center (.compass port, scaledLength) slot) := by
    have strict :=
      retainedFallbackSourcePrefix_dropLast_strictlyAvoids_suffix
        RetainedFallbackFanKind.ordinary route terminal slot
        routeLengthTwo classified factorPositive clearance
        routeSimple routeOrthogonal trivial
    rw [scaledTerminalEq] at strict
    simpa [scaledRoute, center] using strict
  have cancelled :=
    boundedCancellation_forwardCardinalFallback_of_geometry
      scaledRoute port scaledLength slot distance scaledRouteLengthThree
      scaledClassifiedPort scaledOrthogonal sourcePrefixSimple cardinal
      scaledLengthLarge shiftStrict predecessor sourceStrict
  have suffixDirections :
      Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (retainedFallbackFanSuffixRouteAt
              .ordinary center (.compass port, scaledLength) slot)) =
        fanWord := by
    simpa [fanWord, scaledTerminalEq'] using
      retainedFallbackFanSuffixRouteAt_normalized_directions
        .ordinary center (.compass port, scaledLength) slot
        (by omega) trivial
  rw [suffixDirections] at cancelled
  have sourceTake := retainedFallbackSourcePrefix_forward_take
    scaledRoute port scaledLength slot distance scaledRouteLengthThree
    scaledClassifiedPort scaledOrthogonal cardinal shiftStrict predecessor
  have fanDrop :=
    retainedNormalizedFallbackFanSuffixDirections_forward_drop
      center port scaledLength slot (by omega)
      (by
        rcases cardinal with rfl | rfl | rfl | rfl <;>
          simp [retainedTerminalFanOuterRadialLength,
            retainedTerminalFanTotalRefinement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalInterfaceMultiplier] at scaledLengthLarge ⊢ <;>
          omega)
      cardinal
  have sourceTake' :
      sourceWord.take (sourceWord.length - trim) =
        retainedFallbackCardinalForwardKeptDirections
          scaledRoute port scaledLength slot distance := by
    simpa [sourceWord, trim] using sourceTake
  have fanDrop' :
      fanWord.drop trim =
        retainedFallbackCardinalForwardRestDirections
          center port scaledLength slot := by
    simpa [fanWord, trim, scaledTerminalEq'] using fanDrop
  change
    BoundedDelimitedDirectionCancellation.output
        (DelimitedRouteJoin.delimited (sourceWord ++ fanWord)) =
      DelimitedRouteJoin.delimited
        (sourceWord.take (sourceWord.length - trim) ++ fanWord.drop trim)
  calc
    _ = DelimitedRouteJoin.delimited
          (retainedFallbackCardinalForwardKeptDirections
              scaledRoute port scaledLength slot distance ++
            retainedFallbackCardinalForwardRestDirections
              center port scaledLength slot) := by
      simpa [center] using cancelled
    _ = _ := by rw [sourceTake', fanDrop']

end PeriodicEightOccurrenceSplit
end LeanTrominoes
