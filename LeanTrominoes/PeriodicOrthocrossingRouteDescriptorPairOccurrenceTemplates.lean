/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossings
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegments

/-! # Finite affine neighboring-occurrence templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- One affine segment template with its fixed within-route index and one
fixed neighboring lattice translation. -/
structure Occurrence where
  segmentIndex : Nat
  segment : Segment
  translate : Cell
  deriving DecidableEq

/-- Interpret an occurrence template as the corresponding self-indexed
semantic segment occurrence. -/
def Occurrence.evalPair
    (occurrence : Occurrence) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) : IndexedGridSegment × Cell :=
  (⟨(descriptorAt pair side).edgeIndex, occurrence.segmentIndex,
      occurrence.segment.evalPair pair⟩,
    occurrence.translate)

/-- Affine geometry of this occurrence after translation by the common
period stored in the first descriptor of the ordered pair. -/
def Occurrence.segmentAtFirstPeriod (occurrence : Occurrence) : Segment :=
  occurrence.segment.translateByPeriod (gridSize .first) occurrence.translate

/-- All at-most-eighty-one neighboring occurrences of one finite route shape. -/
def RouteShape.occurrences
    (shape : RouteShape) (side : Side) : List Occurrence :=
  (shape.segments side).zipIdx.flatMap fun taggedSegment =>
    neighborTranslations.map fun translate =>
      ⟨taggedSegment.2, taggedSegment.1, translate⟩

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
