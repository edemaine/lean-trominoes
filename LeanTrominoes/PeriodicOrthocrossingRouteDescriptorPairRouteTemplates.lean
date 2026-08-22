/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCoreTemplates

/-! # Complete finite affine templates for local descriptor routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Which endpoint fanout of a descriptor route is being selected. -/
inductive Endpoint
  | source
  | target
  deriving DecidableEq, Fintype

/-- A straight two-point fanout or a bent three-point fanout. -/
inductive FanoutShape
  | straight
  | bent
  deriving DecidableEq, Fintype

/-- The affine vertex-center column at one endpoint. -/
def Endpoint.centerX : Endpoint → Side → Expression
  | .source, side => sourceCenterX side
  | .target, side => targetCenterX side

/-- The affine port column at one endpoint. -/
def Endpoint.portX : Endpoint → Side → Expression
  | .source, side => sourcePortX side
  | .target, side => targetPortX side

/-- The semantic condition selecting one fanout shape. -/
def FanoutShape.Matches
    (shape : FanoutShape) (endpoint : Endpoint)
    (descriptor : RouteDescriptor) : Prop :=
  let center := match endpoint with
    | .source => vertexX descriptor.sourceVertexIndex
    | .target => vertexX descriptor.targetVertexIndex
  let port := match endpoint with
    | .source => descriptorPortX descriptor.sourceVertexIndex
        descriptor.sourcePortRank
    | .target => descriptorPortX descriptor.targetVertexIndex
        descriptor.targetPortRank
  match shape with
  | .straight => center = port
  | .bent => center ≠ port

instance FanoutShape.matchesDecidable
    (shape : FanoutShape) (endpoint : Endpoint)
    (descriptor : RouteDescriptor) :
    Decidable (shape.Matches endpoint descriptor) := by
  cases shape <;> cases endpoint <;>
    unfold FanoutShape.Matches <;> infer_instance

/-- Exact affine guard selecting one endpoint fanout shape. -/
def FanoutShape.guard
    (shape : FanoutShape) (endpoint : Endpoint) (side : Side) : Predicate :=
  match shape with
  | .straight => equal (endpoint.centerX side) (endpoint.portX side)
  | .bent => .negation (equal
      (endpoint.centerX side) (endpoint.portX side))

/-- Affine point list of the source endpoint fanout. -/
def FanoutShape.sourcePoints
    (shape : FanoutShape) (side : Side) : List Point :=
  let centerX := sourceCenterX side
  let portX := sourcePortX side
  match shape with
  | .straight => [point centerX (constant 2), point portX (constant 3)]
  | .bent =>
      [point centerX (constant 2), point portX (constant 2),
        point portX (constant 3)]

/-- Translate an affine point by the local period offset selected by a core
shape. -/
def CoreShape.translatePoint
    (shape : CoreShape) (side : Side) (affinePoint : Point) : Point :=
  let size := gridSize side
  match shape with
  | .zero => affinePoint
  | .positiveHorizontalDirect | .positiveHorizontalBent =>
      point (affinePoint.horizontal.add size) affinePoint.vertical
  | .negativeHorizontalDirect | .negativeHorizontalBent =>
      point (affinePoint.horizontal.subtract size) affinePoint.vertical
  | .positiveVertical =>
      point affinePoint.horizontal (affinePoint.vertical.add size)
  | .negativeVertical =>
      point affinePoint.horizontal (affinePoint.vertical.subtract size)

/-- Tail of the translated, reversed target fanout.  Its omitted first point
is the target port already present as the last core point. -/
def FanoutShape.targetTail
    (shape : FanoutShape) (coreShape : CoreShape) (side : Side) : List Point :=
  let centerAtTwo := point (targetCenterX side) (constant 2)
  let portAtTwo := point (targetPortX side) (constant 2)
  match shape with
  | .straight => [coreShape.translatePoint side centerAtTwo]
  | .bent =>
      [coreShape.translatePoint side portAtTwo,
        coreShape.translatePoint side centerAtTwo]

/-- Complete affine route point list for three finite shape choices. -/
def routePoints
    (sourceShape : FanoutShape) (coreShape : CoreShape)
    (targetShape : FanoutShape) (side : Side) : List Point :=
  sourceShape.sourcePoints side ++
    (coreShape.points side).tail ++
    targetShape.targetTail coreShape side

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
