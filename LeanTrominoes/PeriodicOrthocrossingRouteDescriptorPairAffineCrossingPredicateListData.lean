/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingPredicate
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection

/-! # Compact fixed affine crossing predicate lists -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- One fixed predicate combines both route-shape guards with one occurrence-
pair crossing test. -/
def guardedCrossingPredicate
    (shapes : RouteShape × RouteShape)
    (occurrences : Occurrence × Occurrence) : Predicate :=
  all [shapes.1.guard .first, shapes.2.guard .second,
    crossingPredicate occurrences.1 occurrences.2]

/-- All guarded occurrence tests belonging to one route-shape pair. -/
def routeShapePairCrossingPredicates
    (shapes : RouteShape × RouteShape) : List Predicate :=
  (shapes.1.occurrences .first ×ˢ shapes.2.occurrences .second).map
    (guardedCrossingPredicate shapes)

/-- Complete compact predicate list for the twenty-eight-squared affine
shape scan. -/
def affineCrossingPredicates : List Predicate :=
  (allRouteShapes ×ˢ allRouteShapes).flatMap
    routeShapePairCrossingPredicates

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
