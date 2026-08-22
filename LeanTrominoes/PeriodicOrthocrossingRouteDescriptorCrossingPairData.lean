/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Canonical crossing pairs reconstructed from route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Recover the common drawing period from the first route descriptor.  The
empty default is irrelevant for canonical nonempty incidence streams. -/
def routeDescriptorStreamGridSize : List RouteDescriptor → Nat
  | descriptor :: _ => descriptor.gridSize
  | [] => 0

/-- Indexed segments reconstructed from a bare route-descriptor list. -/
def routeDescriptorIndexedSegments
    (descriptors : List RouteDescriptor) : List IndexedGridSegment :=
  (descriptors.map RouteDescriptor.route).zipIdx.flatMap fun taggedRoute =>
    (gridPolylineSegments taggedRoute.1).zipIdx.map fun taggedSegment =>
      ⟨taggedRoute.2, taggedSegment.2, taggedSegment.1⟩

/-- The fixed nine neighboring translations of every reconstructed segment. -/
def routeDescriptorNeighborOccurrences
    (descriptors : List RouteDescriptor) :
    List (IndexedGridSegment × Cell) :=
  (routeDescriptorIndexedSegments descriptors).flatMap fun indexed =>
    neighborTranslations.map fun translate => (indexed, translate)

/-- Ordered canonical crossing pairs reconstructed solely from the drawing
period and a route-descriptor list. -/
def routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  (routeDescriptorNeighborOccurrences descriptors ×ˢ
      routeDescriptorNeighborOccurrences descriptors).filter
    (canonicalOrientedOccurrencePairAtPeriod period)

/-- Number of canonical crossing pairs reconstructed from compact numeric
route data. -/
def routeDescriptorOrientedCrossingCountAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) : Nat :=
  (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
    period descriptors).length

/-- Canonical crossing pairs using the period repeated in the descriptor
stream itself. -/
def routeDescriptorOrientedCrossingOccurrencePairs
    (descriptors : List RouteDescriptor) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
    (routeDescriptorStreamGridSize descriptors) descriptors

/-- Canonical crossing count using only a descriptor stream. -/
def routeDescriptorOrientedCrossingCount
    (descriptors : List RouteDescriptor) : Nat :=
  (routeDescriptorOrientedCrossingOccurrencePairs descriptors).length

end PeriodicOrthocrossing
end LeanTrominoes
