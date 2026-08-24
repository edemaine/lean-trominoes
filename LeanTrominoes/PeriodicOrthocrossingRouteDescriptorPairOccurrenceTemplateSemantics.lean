/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateEvaluationSemantics

/-! # Exact semantics of affine neighboring-occurrence templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The affine translated segment of an occurrence template evaluates to the
same geometry as `occurrenceSegmentAtPeriod` at the first descriptor's period. -/
theorem Occurrence.evalPair_segmentAtFirstPeriod
    (occurrence : Occurrence) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    occurrence.segmentAtFirstPeriod.evalPair pair =
      occurrenceSegmentAtPeriod pair.1.gridSize
        (occurrence.evalPair side pair) := by
  have sizeEq :
      Expression.eval (pairFieldValue pair) (gridSize .first) =
        (pair.1.gridSize : Int) :=
    evalPair_gridSize pair .first
  unfold Occurrence.segmentAtFirstPeriod Segment.evalPair
    Occurrence.evalPair occurrenceSegmentAtPeriod
  rw [Segment.eval_translateByPeriod]
  rw [sizeEq]
  rfl

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
