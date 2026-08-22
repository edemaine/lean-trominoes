/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSegments
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteTemplates

/-! # Finite affine route shapes and their segment templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- One of the twenty-eight finite local route shapes. -/
structure RouteShape where
  source : FanoutShape
  core : CoreShape
  target : FanoutShape
  deriving DecidableEq, Fintype

/-- Semantic condition selecting all three components of a route shape. -/
def RouteShape.Matches
    (shape : RouteShape) (descriptor : RouteDescriptor) : Prop :=
  shape.source.Matches .source descriptor ∧
    shape.core.Matches descriptor ∧
    shape.target.Matches .target descriptor

instance RouteShape.matchesDecidable
    (shape : RouteShape) (descriptor : RouteDescriptor) :
    Decidable (shape.Matches descriptor) := by
  unfold RouteShape.Matches
  infer_instance

/-- Fixed combined affine guard for a complete route shape. -/
def RouteShape.guard (shape : RouteShape) (side : Side) : Predicate :=
  all [shape.source.guard .source side, shape.core.guard side,
    shape.target.guard .target side]

/-- Complete affine point list selected by a route shape. -/
def RouteShape.points (shape : RouteShape) (side : Side) : List Point :=
  routePoints shape.source shape.core shape.target side

/-- Complete affine consecutive-segment list selected by a route shape. -/
def RouteShape.segments (shape : RouteShape) (side : Side) : List Segment :=
  RouteDescriptorPairAffine.segments (shape.points side)

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
