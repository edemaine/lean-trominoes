/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirectionTranslation

/-! # Translation of forward-cardinal normalized fallbacks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Translating a raw source route preserves the trimmed normalized word
supplied by the forward-cardinal tangent theorem. -/
theorem scaledSplicedOwnFigure7Route_forwardCardinalTangent_translate_normalized_directions
    {factor : Nat}
    (offset : Cell)
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
    (terminalLengthPositive : 0 < terminal.2)
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
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline factor (translatePolyline offset route))
            (scaleRetainedTerminalData factor terminal) slot)) =
      (Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route))).take
          ((Gadget.unitSubdivisionDirections
              (retainedFallbackSourcePrefix
                (scalePolyline factor route))).length -
            retainedTerminalFanOuterLaneSpacing * slot.val) ++
        (retainedNormalizedFallbackFanSuffixDirections
          .ordinary (scaleRetainedTerminalData factor terminal) slot).drop
            (retainedTerminalFanOuterLaneSpacing * slot.val) := by
  have routeLengthTwo : 2 ≤ route.length := by omega
  calc
    Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
              (scalePolyline factor (translatePolyline offset route))
              (scaleRetainedTerminalData factor terminal) slot)) =
        Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
              (scalePolyline factor route)
              (scaleRetainedTerminalData factor terminal) slot)) :=
      RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_translate_normalized_directions
        .ordinary offset route terminal slot factorPositive routeLengthTwo
        classified routeOrthogonal terminalLengthPositive trivial
    _ = (Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route))).take
          ((Gadget.unitSubdivisionDirections
              (retainedFallbackSourcePrefix
                (scalePolyline factor route))).length -
            retainedTerminalFanOuterLaneSpacing * slot.val) ++
        (retainedNormalizedFallbackFanSuffixDirections
          .ordinary (scaleRetainedTerminalData factor terminal) slot).drop
            (retainedTerminalFanOuterLaneSpacing * slot.val) :=
      scaledSplicedOwnFigure7Route_forwardCardinalTangent_normalized_directions
        route terminal slot port scaledLength distance factorPositive
        clearance routeLength classified routeSimple routeOrthogonal
        terminalLengthPositive scaledTerminalEq cardinal scaledLengthLarge
        shiftStrict predecessor

end PeriodicEightOccurrenceSplit
end LeanTrominoes
