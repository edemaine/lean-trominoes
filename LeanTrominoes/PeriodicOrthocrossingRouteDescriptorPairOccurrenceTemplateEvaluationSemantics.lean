/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplates
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegmentSemantics

/-! # Evaluation semantics of affine neighboring-occurrence templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Indexed affine segments of a selected route shape evaluate to the exact
self-indexed semantic segment block. -/
theorem RouteShape.map_evalPair_indexedSegments
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    ((shape.segments side).zipIdx.map fun taggedSegment =>
        IndexedGridSegment.mk (descriptorAt pair side).edgeIndex
          taggedSegment.2 (taggedSegment.1.evalPair pair)) =
      (descriptorAt pair side).indexedSegments
        (descriptorAt pair side).edgeIndex := by
  have segmentEq := shape.map_evalPair_segments side pair shapeMatches
  unfold RouteDescriptor.indexedSegments
  rw [← segmentEq]
  rw [List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro taggedSegment taggedSegmentMem
  rfl

/-- The complete affine neighboring-occurrence list evaluates exactly to the
descriptor's semantic self-indexed neighboring occurrences. -/
theorem RouteShape.map_evalPair_occurrences
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.occurrences side).map (fun occurrence =>
        occurrence.evalPair side pair) =
      (descriptorAt pair side).selfIndexedNeighborOccurrences := by
  have indexedEq := shape.map_evalPair_indexedSegments side pair shapeMatches
  unfold RouteShape.occurrences Occurrence.evalPair
    RouteDescriptor.selfIndexedNeighborOccurrences
    RouteDescriptor.neighborOccurrences
  rw [List.map_flatMap]
  rw [← indexedEq]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedSegment taggedSegmentMem
  rw [List.map_map]
  apply List.map_congr_left
  intro translate translateMem
  rfl

/-- Every finite route shape contributes at most eighty-one occurrence
templates after the fixed nine neighboring translations. -/
theorem RouteShape.occurrences_length_le_eightyOne
    (shape : RouteShape) (side : Side) :
    (shape.occurrences side).length ≤ 81 := by
  unfold RouteShape.occurrences
  rw [List.length_flatMap]
  simp only [List.length_map]
  have segmentBound := shape.segments_length_le_nine side
  simp [neighborTranslations, neighborCoordinates]
  omega

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
