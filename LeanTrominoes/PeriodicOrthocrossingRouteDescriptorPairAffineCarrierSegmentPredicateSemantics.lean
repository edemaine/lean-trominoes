/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics

/-! # Semantics of affine carrier-segment predicates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The carrier diagonal predicate compares exactly the stored edge indices. -/
@[simp] theorem carrierSegmentSameEdgeIndex_evalPair
    (pair : RouteDescriptor × RouteDescriptor) :
    carrierSegmentSameEdgeIndex.evalPair pair =
      decide (pair.1.edgeIndex = pair.2.edgeIndex) := by
  rcases pair with ⟨first, second⟩
  rcases first with
    ⟨firstVertexCount, firstEdgeCount, firstEdgeIndex,
      firstSourceVertexIndex, firstTargetVertexIndex,
      firstSourcePortRank, firstTargetPortRank, firstOffset⟩
  rcases second with
    ⟨secondVertexCount, secondEdgeCount, secondEdgeIndex,
      secondSourceVertexIndex, secondTargetVertexIndex,
      secondSourcePortRank, secondTargetPortRank, secondOffset⟩
  simp [carrierSegmentSameEdgeIndex, Predicate.evalPair, Predicate.eval,
    Atom.eval, Relation.eval, Expression.eval, Term.eval, term,
    pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
    signedUnaryFields, field, equal, compare]

/-- The local horizontal predicate recognizes exactly the evaluated segment. -/
@[simp] theorem Segment.carrierIsHorizontal_evalPair
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) :
    segment.carrierIsHorizontal.evalPair pair =
      decide (segment.evalPair pair).IsHorizontal := by
  simp [Segment.carrierIsHorizontal, evalPair_all,
    Segment.evalPair, Segment.eval, Point.eval, Expression.evalPair,
    GridSegment.IsHorizontal]
  rfl

/-- The local vertical predicate recognizes exactly the evaluated segment. -/
@[simp] theorem Segment.carrierIsVertical_evalPair
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) :
    segment.carrierIsVertical.evalPair pair =
      decide (segment.evalPair pair).IsVertical := by
  simp [Segment.carrierIsVertical, evalPair_all,
    Segment.evalPair, Segment.eval, Point.eval, Expression.evalPair,
    GridSegment.IsVertical]
  rfl

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
