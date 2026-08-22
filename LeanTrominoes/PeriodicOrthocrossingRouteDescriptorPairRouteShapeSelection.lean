/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegments

/-! # Finite selection of local affine route shapes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Both endpoint fanout shapes in fixed order. -/
def allFanoutShapes : List FanoutShape :=
  [.straight, .bent]

/-- All seven local core shapes in fixed branch order. -/
def allCoreShapes : List CoreShape :=
  [.zero, .positiveHorizontalDirect, .positiveHorizontalBent,
    .negativeHorizontalDirect, .negativeHorizontalBent,
    .positiveVertical, .negativeVertical]

/-- All twenty-eight complete local route shapes in row-major order. -/
def allRouteShapes : List RouteShape :=
  allFanoutShapes.flatMap fun source =>
    allCoreShapes.flatMap fun core =>
      allFanoutShapes.map fun target => ⟨source, core, target⟩

/-- Select the unique straight/bent shape of one endpoint fanout. -/
def FanoutShape.select
    (endpoint : Endpoint) (descriptor : RouteDescriptor) : FanoutShape :=
  if FanoutShape.straight.Matches endpoint descriptor then
    .straight
  else
    .bent

/-- Select the unique local core branch, rejecting a nonlocal offset. -/
def CoreShape.select? (descriptor : RouteDescriptor) : Option CoreShape :=
  let sourceX := descriptorPortX descriptor.sourceVertexIndex
    descriptor.sourcePortRank
  let targetX := descriptorPortX descriptor.targetVertexIndex
    descriptor.targetPortRank
  match descriptor.offset with
  | (0, 0) => some .zero
  | (1, 0) =>
      if targetX < sourceX then
        some .positiveHorizontalDirect
      else
        some .positiveHorizontalBent
  | (-1, 0) =>
      if sourceX < targetX then
        some .negativeHorizontalDirect
      else
        some .negativeHorizontalBent
  | (0, 1) => some .positiveVertical
  | (0, -1) => some .negativeVertical
  | _ => none

/-- Select the unique complete route shape whenever the descriptor offset is
one of the five local lattice offsets. -/
def RouteShape.select? (descriptor : RouteDescriptor) : Option RouteShape :=
  (CoreShape.select? descriptor).map fun core =>
    ⟨FanoutShape.select .source descriptor, core,
      FanoutShape.select .target descriptor⟩

/-- A descriptor is locally shaped when one of the twenty-eight finite route
shapes matches it. -/
def RouteDescriptor.HasLocalShape (descriptor : RouteDescriptor) : Prop :=
  ∃ shape : RouteShape, shape.Matches descriptor

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
