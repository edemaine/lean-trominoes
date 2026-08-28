/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingHaloData
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Canonical crossing compact-word source streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingCompactAtomWordSources

/-- The graph-free canonical crossing list reconstructed from a numeric route
descriptor stream. -/
def crossingsAtPeriod (period : Nat)
    (descriptors : List RouteDescriptor) : List CrossingRecord :=
  occurrencePairCanonicalizedCrossingHaloAtPeriod period
    (routeDescriptorNeighborOccurrences descriptors)

/-- One tagged canonical-left source pair per canonical crossing, in exact
last-physical-occurrence order. -/
def wordsAtPeriod (period : Nat)
    (descriptors : List RouteDescriptor) : List (List Bool) :=
  (crossingsAtPeriod period descriptors).map fun crossing =>
    true :: CarrierNodeSourceKeys.word
      (RetainedCompactAtomWords.crossingPair crossing)

end CanonicalCrossingCompactAtomWordSources
end LeanTrominoes.PeriodicOrthocrossing
