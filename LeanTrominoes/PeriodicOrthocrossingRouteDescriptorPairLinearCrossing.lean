/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairLinearPredicate
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData

/-! # Linearized crossing counts for route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Pair-local crossing count expressed only through the oriented linear
occurrence predicate. -/
def routeDescriptorPairLinearCrossingCountAtPeriod
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor) : Nat :=
  List.filteredProductCount
    (canonicalOrientedOccurrencePairLinearAtPeriod period)
    pair.1.selfIndexedNeighborOccurrences
    pair.2.selfIndexedNeighborOccurrences

/-- Linearized pair-local counts are definitionally scanning the same
occurrences and accept exactly the same entries. -/
theorem routeDescriptorPairCrossingCountAtPeriod_eq_linear
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor) :
    routeDescriptorPairCrossingCountAtPeriod period pair =
      routeDescriptorPairLinearCrossingCountAtPeriod period pair := by
  unfold routeDescriptorPairCrossingCountAtPeriod
    routeDescriptorPairLinearCrossingCountAtPeriod
  rw [show canonicalOrientedOccurrencePairAtPeriod period =
      canonicalOrientedOccurrencePairLinearAtPeriod period by
    funext occurrencePair
    exact canonicalOrientedOccurrencePairAtPeriod_eq_linear
      period occurrencePair]

/-- The thirteen-marker block can therefore be computed from the linearized
predicate without changing its semantic output. -/
theorem routeDescriptorPairCrossingMarkersAtPeriod_eq_linear
    (marker : α) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) :
    routeDescriptorPairCrossingMarkersAtPeriod marker period pair =
      List.replicate
        (13 * routeDescriptorPairLinearCrossingCountAtPeriod period pair)
        marker := by
  unfold routeDescriptorPairCrossingMarkersAtPeriod
  rw [routeDescriptorPairCrossingCountAtPeriod_eq_linear]

end PeriodicOrthocrossing
end LeanTrominoes
