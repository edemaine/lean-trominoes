/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorLocalSegments

/-! # Axis candidates for neighboring route-segment occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The provisional current-slice axis bits attached to one neighboring
segment occurrence. -/
def carrierOccurrenceAxisBit
    (occurrence : IndexedGridSegment × Cell) : Bool × Bool :=
  (decide occurrence.1.segment.IsHorizontal, false)

/-- Axis candidates contributed by one self-indexed route descriptor. -/
def RouteDescriptor.carrierSegmentBitCandidates
    (descriptor : RouteDescriptor) : List (Bool × Bool) :=
  (gridPolylineSegments descriptor.route).flatMap fun segment =>
    neighborTranslations.map fun _ =>
      (decide segment.IsHorizontal, false)

/-- Descriptor-major axis candidates of a complete route stream. -/
def routeDescriptorCarrierSegmentBitCandidates
    (descriptors : List RouteDescriptor) : List (Bool × Bool) :=
  descriptors.flatMap RouteDescriptor.carrierSegmentBitCandidates

end LeanTrominoes.PeriodicOrthocrossing
