/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineBendTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates
import LeanTrominoes.PeriodicOrthocrossingBendCornerGeometry

/-! # Affine route-bend compass-port predicates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PlanarThreeSAT

/-- Recognize one genuine directed axis between two affine points. -/
def directionPredicate
    (first second : Point) : AxisDirection → Predicate
  | .east => all
      [equal first.vertical second.vertical,
        less first.horizontal second.horizontal]
  | .north => all
      [equal first.horizontal second.horizontal,
        less first.vertical second.vertical]
  | .west => all
      [equal first.vertical second.vertical,
        less second.horizontal first.horizontal]
  | .south => all
      [equal first.horizontal second.horizontal,
        less second.vertical first.vertical]
  | .invalid => .falsity

/-- Direction of travel entering the bend through a named outward-facing
corner port. -/
def incomingTravelDirection : CornerPort → AxisDirection
  | .west => .east
  | .east => .west
  | .south => .north
  | .north => .south

/-- Direction of travel leaving the bend through a named corner port. -/
def outgoingTravelDirection : CornerPort → AxisDirection
  | .west => .west
  | .east => .east
  | .south => .south
  | .north => .north

/-- Recognize the ordered incoming and outgoing compass ports of one affine
bend template. -/
def BendTemplate.portPredicate
    (template : BendTemplate)
    (incoming outgoing : CornerPort) : Predicate :=
  all
    [directionPredicate template.incomingStart template.bend
      (incomingTravelDirection incoming),
    directionPredicate template.bend template.outgoingFinish
      (outgoingTravelDirection outgoing)]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
