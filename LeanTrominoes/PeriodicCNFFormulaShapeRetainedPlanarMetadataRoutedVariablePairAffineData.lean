/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates

/-! # Affine predicates for the routed-variable descriptor-pair scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Affine expression for a route descriptor's edge index. -/
def routedVariablePairEdgeIndex (side : Side) : Expression :=
  field side 2

/-- Affine expression for a route descriptor's target vertex index. -/
def routedVariablePairTargetVertexIndex (side : Side) : Expression :=
  field side 4

/-- Affine expression for a route descriptor's target port rank. -/
def routedVariablePairTargetPortRank (side : Side) : Expression :=
  field side 6

/-- Select diagonal next-slice occurrence records, which contribute the
three early boundary sites. -/
def routedVariableNextBoundaryAffinePredicate : Predicate :=
  all
    [equal (routedVariablePairEdgeIndex .first)
      (routedVariablePairEdgeIndex .second),
    equal (routedVariablePairTargetPortRank .first) (constant 0),
    equal (horizontalOffset .first) (constant 1),
    equal (verticalOffset .first) (constant 0)]

/-- Join each rank-two cycle record to the current-slice rank-zero occurrence
record for the same variable vertex. -/
def routedVariableCurrentCycleAffinePredicate : Predicate :=
  all
    [equal (routedVariablePairTargetPortRank .first) (constant 2),
    equal (routedVariablePairTargetPortRank .second) (constant 0),
    equal (routedVariablePairTargetVertexIndex .first)
      (routedVariablePairTargetVertexIndex .second),
    equal (horizontalOffset .second) (constant 0),
    equal (verticalOffset .second) (constant 0)]

/-- Join each rank-two cycle record to the next-slice rank-zero occurrence
record for the same variable vertex. -/
def routedVariableNextCycleAffinePredicate : Predicate :=
  all
    [equal (routedVariablePairTargetPortRank .first) (constant 2),
    equal (routedVariablePairTargetPortRank .second) (constant 0),
    equal (routedVariablePairTargetVertexIndex .first)
      (routedVariablePairTargetVertexIndex .second),
    equal (horizontalOffset .second) (constant 1),
    equal (verticalOffset .second) (constant 0)]

/-- The three routed-variable decisions evaluated together for one pair. -/
def routedVariablePairAffinePredicates : List Predicate :=
  [routedVariableNextBoundaryAffinePredicate,
    routedVariableCurrentCycleAffinePredicate,
    routedVariableNextCycleAffinePredicate]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
