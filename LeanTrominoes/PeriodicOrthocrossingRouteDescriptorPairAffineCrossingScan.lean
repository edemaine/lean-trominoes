/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductCount
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingPredicate
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection

/-! # Finite affine crossing scan for one route-descriptor pair -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Number of accepted occurrence pairs for two fixed affine route shapes. -/
def routeShapePairCrossingCount
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (shapes : RouteShape × RouteShape) : Nat :=
  List.filteredProductCount
    (fun occurrences =>
      (crossingPredicate occurrences.1 occurrences.2).evalTokens tokens)
    (shapes.1.occurrences .first)
    (shapes.2.occurrences .second)

/-- Both affine route-shape guards hold on the tagged descriptor-pair block. -/
def routeShapePairEnabled
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (shapes : RouteShape × RouteShape) : Bool :=
  (shapes.1.guard .first).evalTokens tokens &&
    (shapes.2.guard .second).evalTokens tokens

/-- One shape pair contributes its crossing count exactly when both of its
route guards hold. -/
def guardedRouteShapePairCrossingCount
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (shapes : RouteShape × RouteShape) : Nat :=
  if routeShapePairEnabled tokens shapes then
    routeShapePairCrossingCount tokens shapes
  else
    0

/-- Fixed finite evaluator: test all twenty-eight squared shape guards, then
all at-most-eighty-one squared affine occurrence pairs of each enabled pair. -/
def affineCrossingCount
    (tokens : List RouteDescriptorPairFieldTags.Token) : Nat :=
  ((allRouteShapes ×ˢ allRouteShapes).map
    (guardedRouteShapePairCrossingCount tokens)).sum

/-- Thirteen output markers per crossing accepted by the finite affine scan. -/
def affineCrossingMarkers
    (marker : α) (tokens : List RouteDescriptorPairFieldTags.Token) : List α :=
  List.replicate (13 * affineCrossingCount tokens) marker

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
