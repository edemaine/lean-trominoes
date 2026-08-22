/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineBendPortPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics

/-! # Exact semantics of affine route-bend port predicates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

/-- The affine coordinate test recognizes each genuine axis direction
exactly. -/
theorem directionPredicate_evalPair
    (first second : Point)
    (direction : AxisDirection)
    (genuine : direction.IsGenuine)
    (pair : RouteDescriptor × RouteDescriptor) :
    (directionPredicate first second direction).evalPair pair =
      decide (AxisDirection.between
        (first.evalPair pair) (second.evalPair pair) = direction) := by
  cases direction <;>
    simp_all [directionPredicate, AxisDirection.IsGenuine,
      Point.evalPair, Point.eval, Expression.evalPair,
      AxisDirection.between_eq_east_iff,
      AxisDirection.between_eq_north_iff,
      AxisDirection.between_eq_west_iff,
      AxisDirection.between_eq_south_iff] <;>
    rfl

/-- The combined affine port test is exactly the evaluated route bend's two
ordered compass ports. -/
theorem BendTemplate.portPredicate_evalPair
    (template : BendTemplate)
    (incoming outgoing : CornerPort)
    (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (incomingGenuine :
      (AxisDirection.between
        (template.incomingStart.evalPair pair)
        (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      (AxisDirection.between
        (template.bend.evalPair pair)
        (template.outgoingFinish.evalPair pair)).IsGenuine) :
    (template.portPredicate incoming outgoing).evalPair pair =
      decide
        ((template.evalPair side pair).incomingPort = incoming ∧
          (template.evalPair side pair).outgoingPort = outgoing) := by
  unfold BendTemplate.portPredicate
  simp only [evalPair_all, List.all_cons, List.all_nil,
    Bool.and_true]
  rw [directionPredicate_evalPair _ _ _
      (by cases incoming <;>
        simp [incomingTravelDirection, AxisDirection.IsGenuine]) pair,
    directionPredicate_evalPair _ _ _
      (by cases outgoing <;>
        simp [outgoingTravelDirection, AxisDirection.IsGenuine]) pair]
  cases incoming <;> cases outgoing <;>
    cases incomingDirection : AxisDirection.between
      (template.incomingStart.evalPair pair)
      (template.bend.evalPair pair) <;>
    cases outgoingDirection : AxisDirection.between
      (template.bend.evalPair pair)
      (template.outgoingFinish.evalPair pair) <;>
    simp_all [BendTemplate.evalPair, RouteBend.incomingPort,
      RouteBend.outgoingPort, incomingTravelDirection,
      outgoingTravelDirection, CornerPort.ofDirection,
      AxisDirection.opposite, AxisDirection.IsGenuine]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
