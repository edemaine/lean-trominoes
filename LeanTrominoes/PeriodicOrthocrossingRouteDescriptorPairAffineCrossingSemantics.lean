/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairLinearPredicate
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingPredicate
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateSemantics

/-! # Exact semantics of the affine occurrence-pair crossing predicate -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Field two of either descriptor is its exact stored edge index. -/
theorem evalPair_edgeIndex
    (side : Side) (pair : RouteDescriptor × RouteDescriptor) :
    (field side 2).evalPair pair = (descriptorAt pair side).edgeIndex := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [field, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt]

/-- The affine horizontal predicate is exactly `GridSegment.IsHorizontal`. -/
theorem evalPair_isHorizontal
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) :
    (isHorizontal segment).evalPair pair =
      decide (segment.evalPair pair).IsHorizontal := by
  rcases segment with ⟨start, finish⟩
  simp [isHorizontal, GridSegment.IsHorizontal, Segment.evalPair,
    Segment.eval, Point.eval, Expression.evalPair]
  rfl

/-- The affine vertical predicate is exactly `GridSegment.IsVertical`. -/
theorem evalPair_isVertical
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) :
    (isVertical segment).evalPair pair =
      decide (segment.evalPair pair).IsVertical := by
  rcases segment with ⟨start, finish⟩
  simp [isVertical, GridSegment.IsVertical, Segment.evalPair,
    Segment.eval, Point.eval, Expression.evalPair]
  rfl

/-- The affine interval predicate is exact strict betweenness. -/
theorem evalPair_strictlyBetween
    (first last value : Expression)
    (pair : RouteDescriptor × RouteDescriptor) :
    (strictlyBetween first last value).evalPair pair =
      decide (GridSegment.StrictlyBetween
        (first.evalPair pair) (last.evalPair pair) (value.evalPair pair)) := by
  simp [strictlyBetween, GridSegment.StrictlyBetween]

/-- The affine key predicate is exactly disequality of the two fixed
self-indexed semantic occurrence keys. -/
theorem evalPair_occurrenceKeysDifferent
    (first second : Occurrence)
    (pair : RouteDescriptor × RouteDescriptor) :
    (occurrenceKeysDifferent first second).evalPair pair =
      decide
        (PeriodicGridDrawing.SegmentOccurrenceKey
            (first.evalPair .first pair).1 (first.evalPair .first pair).2 ≠
          PeriodicGridDrawing.SegmentOccurrenceKey
            (second.evalPair .second pair).1
            (second.evalPair .second pair).2) := by
  rw [Bool.eq_iff_iff]
  simp [occurrenceKeysDifferent, Occurrence.evalPair,
    PeriodicGridDrawing.SegmentOccurrenceKey, evalPair_edgeIndex,
    Prod.ext_iff]

/-- For every fixed occurrence-template pair, the affine Boolean formula is
exactly the previously verified linearized canonical crossing predicate. -/
theorem evalPair_crossingPredicate
    (first second : Occurrence)
    (pair : RouteDescriptor × RouteDescriptor) :
    (crossingPredicate first second).evalPair pair =
      canonicalOrientedOccurrencePairLinearAtPeriod pair.1.gridSize
        (first.evalPair .first pair, second.evalPair .second pair) := by
  have sizeEq :
      Expression.eval (pairFieldValue pair) (gridSize .first) =
        (pair.1.gridSize : Int) :=
    evalPair_gridSize pair .first
  unfold canonicalOrientedOccurrencePairLinearAtPeriod
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold canonicalOrientedOccurrencePairLinearConditionsAtPeriod
  dsimp only
  rw [← first.evalPair_segmentAtFirstPeriod .first pair,
    ← second.evalPair_segmentAtFirstPeriod .second pair]
  simp [crossingPredicate,
    evalPair_occurrenceKeysDifferent, evalPair_isHorizontal,
    evalPair_isVertical, evalPair_strictlyBetween,
    Segment.evalPair, Segment.eval, Point.eval, Expression.evalPair, sizeEq]

/-- The same affine formula is exact when evaluated physically on the tagged
descriptor-pair block. -/
theorem evalTokens_crossingPredicate
    (first second : Occurrence)
    (pair : RouteDescriptor × RouteDescriptor) :
    (crossingPredicate first second).evalTokens
        (descriptorPairTokens pair) =
      canonicalOrientedOccurrencePairLinearAtPeriod pair.1.gridSize
        (first.evalPair .first pair, second.evalPair .second pair) := by
  rw [Predicate.evalTokens_descriptorPairTokens,
    evalPair_crossingPredicate]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
