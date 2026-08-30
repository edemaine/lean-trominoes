/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBendRouteNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackCardinalBackwardCancellation
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardCancellationScaled

/-! # Bounded cancellation for every finite bend fallback route -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The already-compiled scaled bend prefix followed by its independently
normalized ordinary fan suffix, before junction cancellation. -/
def bendRoutePreCancellationDirections
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.repeatDirections 1152
      (bendRoutePrefixDirections firstPort secondPort
        localClauseIndex literalIndex) ++
    retainedNormalizedFallbackFanSuffixDirections .ordinary
      (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (bendRouteTerminalData firstPort secondPort
          localClauseIndex literalIndex)) slot

/-- On every genuine in-range entry of the finite bend table, the bounded
junction canceller produces exactly the declarative normalized bend word. -/
theorem boundedCancellation_bendRoutePreCancellationDirections
    (firstPort secondPort : CornerPort)
    (different : firstPort ≠ secondPort)
    (localClauseIndex literalIndex : Nat)
    (clauseLt : localClauseIndex < 2)
    (literalLt : literalIndex < 2)
    (slot : RetainedTerminalSlot) :
    BoundedDelimitedDirectionCancellation.output
        (DelimitedRouteJoin.delimited
          (bendRoutePreCancellationDirections firstPort secondPort
            localClauseIndex literalIndex slot)) =
      DelimitedRouteJoin.delimited
        (bendRouteNormalizedFallbackDirections firstPort secondPort
          localClauseIndex literalIndex slot) := by
  let route := cornerEqualityRoutes firstPort secondPort
    localClauseIndex literalIndex
  let terminal := bendRouteTerminalData firstPort secondPort
    localClauseIndex literalIndex
  let data := bendRouteCardinalTangentData firstPort secondPort
    localClauseIndex literalIndex
  have certificate :=
    bendRouteCardinalTangentCertificate_of_ne firstPort secondPort
      different localClauseIndex literalIndex clauseLt literalLt
  have clearance :
      288 < retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor := by
    have cleared :=
      retainedAngularFanSourceClearanceFactor_clears_transverseBand
    omega
  cases orientationEq :
      bendRouteCardinalTangentOrientation firstPort secondPort
        localClauseIndex literalIndex with
  | backward =>
      have predecessor := certificate.predecessor slot
      rw [orientationEq] at predecessor
      simp only [BendRouteCardinalTangentOrientation.signedDistance]
        at predecessor
      have cancelled :=
        boundedCancellation_backwardCardinalFallback
          route terminal slot data.port data.scaledLength data.distance
          retainedAngularFanSourceClearanceFactor_pos clearance
          certificate.routeLength certificate.classified
          certificate.routeSimple certificate.routeOrthogonal
          certificate.terminalLengthPositive certificate.scaledTerminalEq
          certificate.cardinal certificate.scaledLengthLarge
          certificate.distancePositive predecessor
      rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
        at cancelled
      simpa [route, terminal, data,
        bendRoutePreCancellationDirections,
        bendRouteNormalizedFallbackDirections, orientationEq,
        bendRoutePrefixDirections] using cancelled
  | forward =>
      have predecessor := certificate.predecessor slot
      rw [orientationEq] at predecessor
      simp only [BendRouteCardinalTangentOrientation.signedDistance]
        at predecessor
      have cancelled :=
        boundedCancellation_scaledForwardCardinalFallback
          route terminal slot data.port data.scaledLength data.distance
          retainedAngularFanSourceClearanceFactor_pos clearance
          certificate.routeLength certificate.classified
          certificate.routeSimple certificate.routeOrthogonal
          certificate.scaledTerminalEq certificate.cardinal
          certificate.scaledLengthLarge (certificate.shiftStrict slot)
          predecessor
      rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
        at cancelled
      simpa [route, terminal, data,
        bendRoutePreCancellationDirections,
        bendRouteNormalizedFallbackDirections, orientationEq,
        bendRoutePrefixDirections] using cancelled

end PeriodicEightOccurrenceSplit
end LeanTrominoes
