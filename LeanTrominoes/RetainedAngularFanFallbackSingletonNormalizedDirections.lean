/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackRouteLocalizedNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackRouteSimplicity
import LeanTrominoes.RetainedAngularFanSourceScaledSeparation

/-! # Normalized directions for singleton-prefix fallbacks

When deleting the old target leaves one source point, that point is exactly
the fallback gate.  Consequently the source prefix and fan suffix can meet
only there, with no additional geometric separation argument.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- A source-first-scaled fallback with a singleton retained prefix has the
canonical localized normalized direction word. -/
theorem RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_singleton_normalized_directions
    {factor : Nat}
    (kind : RetainedFallbackFanKind)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (factorPositive : 0 < factor)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeSimple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeOrthogonal : OrthogonalPolyline route)
    (terminalLengthPositive : 0 < terminal.2)
    (valid : kind.Valid
      (scaleRetainedTerminalData factor terminal))
    (singletonPrefix : route.dropLast.length = 1) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route
            (scalePolyline factor route)
            (scaleRetainedTerminalData factor terminal) slot)) =
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route)) ++
        retainedNormalizedFallbackFanSuffixDirections kind
          (scaleRetainedTerminalData factor terminal) slot := by
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let gate :=
    (retainedAngularFanOuterDemand
      (retainedFallbackFanCenter scaledRoute) scaledTerminal slot).gate
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified factorPositive classified
  have scaledSimple :
      LocalIncidenceDrawing.RouteIsSimple scaledRoute := by
    exact routeIsSimple_scalePolyline
      (by exact_mod_cast factorPositive) routeSimple
  have scaledOrthogonal : OrthogonalPolyline scaledRoute := by
    exact routeOrthogonal.scalePolyline
      (by exact_mod_cast factorPositive)
  have scaledLengthPositive : 0 < scaledTerminal.2 := by
    change 0 < (scaleRetainedTerminalData factor terminal).2
    rw [scaleRetainedTerminalData_length]
    exact Nat.mul_pos factorPositive terminalLengthPositive
  have sourcePrefixSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (retainedFallbackSourcePrefix scaledRoute) :=
    retainedFallbackSourcePrefix_isSimple scaledRoute scaledSimple
  have sourcePrefixEq :
      retainedFallbackSourcePrefix scaledRoute = [gate] := by
    simpa [scaledRoute, scaledTerminal, gate,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourceScaledPrefix_eq_singleton_gate
        factorPositive route terminal slot routeLength classified
        singletonPrefix
  have onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline
          (retainedFallbackSourcePrefix scaledRoute) →
        point ∈ AxisDirection.unitSubdividePolyline
          (retainedFallbackFanSuffixRouteAt kind
            (retainedFallbackFanCenter scaledRoute)
            scaledTerminal slot) →
        point = gate := by
    intro point prefixMember _suffixMember
    rw [sourcePrefixEq] at prefixMember
    simpa [AxisDirection.unitSubdividePolyline] using prefixMember
  exact kind.splicedOwnFigure7Route_localized_normalized_directions
    scaledRoute scaledTerminal slot scaledLength scaledClassified
    scaledOrthogonal scaledLengthPositive valid sourcePrefixSimple
    onlyCommon

end PeriodicEightOccurrenceSplit
end LeanTrominoes
