/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardCancellationSuffix

/-! # Bounded cancellation at a forward-cardinal fan junction -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- The bounded direction transducer removes exactly the equal forward and
backward lane-overlap blocks.  The remaining word is assumed nonreversing;
the geometric route proof supplies this fact separately. -/
theorem boundedCancellation_forwardCardinalFallback
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (.compass port, length))
    (routeOrthogonal : OrthogonalPolyline route)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthPositive : 0 < length)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, length))
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix route).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter route)
              (.compass port, length) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port)))))
    (targetNoReversal :
      BoundedDelimitedDirectionCancellation.HasNoImmediateReversal
        (retainedFallbackCardinalForwardKeptDirections
            route port length slot distance ++
          retainedFallbackCardinalForwardRestDirections
            (retainedFallbackFanCenter route) port length slot)) :
    BoundedDelimitedDirectionCancellation.output
        (DelimitedRouteJoin.delimited
          (Gadget.unitSubdivisionDirections
              (retainedFallbackSourcePrefix route) ++
            Gadget.unitSubdivisionDirections
              (AxisDirection.normalizeOrthogonalPolyline
                (retainedFallbackFanSuffixRouteAt
                  .ordinary (retainedFallbackFanCenter route)
                  (.compass port, length) slot)))) =
      DelimitedRouteJoin.delimited
        (retainedFallbackCardinalForwardKeptDirections
            route port length slot distance ++
          retainedFallbackCardinalForwardRestDirections
            (retainedFallbackFanCenter route) port length slot) := by
  let kept := retainedFallbackCardinalForwardKeptDirections
    route port length slot distance
  let rest := retainedFallbackCardinalForwardRestDirections
    (retainedFallbackFanCenter route) port length slot
  let direction := retainedTerminalFanCardinalForwardDirection port
  let amount := retainedTerminalFanCardinalCancellationCount slot
  have targetNoReversal' :
      BoundedDelimitedDirectionCancellation.HasNoImmediateReversal
        (kept ++ rest) := by
    simpa [kept, rest] using targetNoReversal
  have sourceDirections :=
    retainedFallbackSourcePrefix_forward_directions
      route port length slot distance routeLength classified
      routeOrthogonal cardinal shiftStrict predecessor
  have suffixDirections :=
    retainedFallbackCardinalForwardNormalizedSuffix_directions
      (retainedFallbackFanCenter route) port length slot
      lengthPositive radialPositive cardinal
  have genuine : direction.IsGenuine := by
    exact retainedTerminalFanCardinalForwardDirection_genuine
      port cardinal
  have keptLast : kept.getLast? = some direction := by
    exact retainedFallbackCardinalForwardKeptDirections_getLast?
      route port length slot distance routeLength routeOrthogonal
      cardinal shiftStrict predecessor
  have keptNonempty : kept ≠ [] := by
    intro empty
    rw [empty] at keptLast
    simp at keptLast
  have keptNoReversal :
      BoundedDelimitedDirectionCancellation.HasNoImmediateReversal kept := by
    have prefixNoReversal := targetNoReversal'.take kept.length
    simpa using prefixNoReversal
  have restNoReversal :
      BoundedDelimitedDirectionCancellation.HasNoImmediateReversal rest := by
    have suffixNoReversal := targetNoReversal'.drop kept.length
    simpa using suffixNoReversal
  have boundary :
      BoundedDelimitedDirectionCancellation.CompatibleHead direction rest :=
    BoundedDelimitedDirectionCancellation.compatibleHead_of_append
      kept rest direction keptLast targetNoReversal'
  have cancelled :=
    BoundedDelimitedDirectionCancellation.output_delimited_append_opposite_blocks
      kept rest direction amount genuine keptNonempty keptLast
      keptNoReversal boundary restNoReversal
  rw [sourceDirections, suffixDirections]
  simpa [kept, rest, direction, amount, List.append_assoc] using cancelled

end PeriodicEightOccurrenceSplit
end LeanTrominoes
