/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplates

/-! # Affine crossing predicate for fixed occurrence templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Affine predicate that one segment is nondegenerate and horizontal. -/
def isHorizontal (segment : Segment) : Predicate :=
  all [equal segment.start.vertical segment.finish.vertical,
    notEqual segment.start.horizontal segment.finish.horizontal]

/-- Affine predicate that one segment is nondegenerate and vertical. -/
def isVertical (segment : Segment) : Predicate :=
  all [equal segment.start.horizontal segment.finish.horizontal,
    notEqual segment.start.vertical segment.finish.vertical]

/-- Affine strict betweenness, independent of endpoint order. -/
def strictlyBetween
    (first last value : Expression) : Predicate :=
  any [all [less first value, less value last],
    all [less last value, less value first]]

/-- The two fixed occurrence templates have different semantic occurrence
keys.  Their route indices are the two descriptor edge-index fields; all
other key coordinates are template constants. -/
def occurrenceKeysDifferent
    (first second : Occurrence) : Predicate :=
  any [
    notEqual (field .first 2) (field .second 2),
    notEqual (constant first.segmentIndex) (constant second.segmentIndex),
    notEqual (constant first.translate.1) (constant second.translate.1),
    notEqual (constant first.translate.2) (constant second.translate.2)]

/-- Complete quantifier-free affine crossing formula for one fixed ordered
pair of neighboring occurrence templates. -/
def crossingPredicate
    (first second : Occurrence) : Predicate :=
  let firstSegment := first.segmentAtFirstPeriod
  let secondSegment := second.segmentAtFirstPeriod
  let period := gridSize .first
  all [
    lessEqual (constant 0) secondSegment.start.horizontal,
    less secondSegment.start.horizontal period,
    lessEqual (constant 0) firstSegment.start.vertical,
    less firstSegment.start.vertical period,
    occurrenceKeysDifferent first second,
    isHorizontal firstSegment,
    isVertical secondSegment,
    strictlyBetween firstSegment.start.horizontal
      firstSegment.finish.horizontal secondSegment.start.horizontal,
    strictlyBetween secondSegment.start.vertical
      secondSegment.finish.vertical firstSegment.start.vertical]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
