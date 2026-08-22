/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebra
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates

/-! # Finite affine templates for local descriptor route cores -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The seven branch shapes of a route core with a local lattice offset. -/
inductive CoreShape
  | zero
  | positiveHorizontalDirect
  | positiveHorizontalBent
  | negativeHorizontalDirect
  | negativeHorizontalBent
  | positiveVertical
  | negativeVertical
  deriving DecidableEq, Fintype

/-- Semantic condition selecting one local core shape. -/
def CoreShape.Matches
    (shape : CoreShape) (descriptor : RouteDescriptor) : Prop :=
  let sourceX := descriptorPortX descriptor.sourceVertexIndex
    descriptor.sourcePortRank
  let targetX := descriptorPortX descriptor.targetVertexIndex
    descriptor.targetPortRank
  match shape with
  | .zero => descriptor.offset = (0, 0)
  | .positiveHorizontalDirect =>
      descriptor.offset = (1, 0) ∧ targetX < sourceX
  | .positiveHorizontalBent =>
      descriptor.offset = (1, 0) ∧ ¬targetX < sourceX
  | .negativeHorizontalDirect =>
      descriptor.offset = (-1, 0) ∧ sourceX < targetX
  | .negativeHorizontalBent =>
      descriptor.offset = (-1, 0) ∧ ¬sourceX < targetX
  | .positiveVertical => descriptor.offset = (0, 1)
  | .negativeVertical => descriptor.offset = (0, -1)

instance CoreShape.matchesDecidable
    (shape : CoreShape) (descriptor : RouteDescriptor) :
    Decidable (shape.Matches descriptor) := by
  cases shape <;> unfold CoreShape.Matches <;> infer_instance

/-- Fixed affine guard selecting one local core shape from tagged fields. -/
def CoreShape.guard (shape : CoreShape) (side : Side) : Predicate :=
  let horizontal := horizontalOffset side
  let vertical := verticalOffset side
  let sourceX := sourcePortX side
  let targetX := targetPortX side
  match shape with
  | .zero =>
      all [equal horizontal (constant 0), equal vertical (constant 0)]
  | .positiveHorizontalDirect =>
      all [equal horizontal (constant 1), equal vertical (constant 0),
        less targetX sourceX]
  | .positiveHorizontalBent =>
      all [equal horizontal (constant 1), equal vertical (constant 0),
        .negation (less targetX sourceX)]
  | .negativeHorizontalDirect =>
      all [equal horizontal (constant (-1)), equal vertical (constant 0),
        less sourceX targetX]
  | .negativeHorizontalBent =>
      all [equal horizontal (constant (-1)), equal vertical (constant 0),
        .negation (less sourceX targetX)]
  | .positiveVertical =>
      all [equal horizontal (constant 0), equal vertical (constant 1)]
  | .negativeVertical =>
      all [equal horizontal (constant 0), equal vertical (constant (-1))]

/-- The complete point list of one local core branch, expressed affinely. -/
def CoreShape.points (shape : CoreShape) (side : Side) : List Point :=
  let zero := constant 0
  let three := constant 3
  let sourceX := sourcePortX side
  let targetX := targetPortX side
  let size := gridSize side
  let low := lowTrack side
  let high := highTrack side
  let gate := gateX side
  let sourcePoint := point sourceX three
  match shape with
  | .zero =>
      [sourcePoint, point sourceX low, point targetX low,
        point targetX three]
  | .positiveHorizontalDirect =>
      let translatedTargetX := targetX.add size
      [sourcePoint, point sourceX low, point translatedTargetX low,
        point translatedTargetX three]
  | .positiveHorizontalBent =>
      let translatedTargetX := targetX.add size
      [sourcePoint, point sourceX low, point size low, point size high,
        point translatedTargetX high, point translatedTargetX three]
  | .negativeHorizontalDirect =>
      let translatedTargetX := targetX.subtract size
      [sourcePoint, point sourceX low, point translatedTargetX low,
        point translatedTargetX three]
  | .negativeHorizontalBent =>
      let translatedTargetX := targetX.subtract size
      [sourcePoint, point sourceX low, point zero low, point zero high,
        point translatedTargetX high, point translatedTargetX three]
  | .positiveVertical =>
      let translatedLow := low.add size
      [sourcePoint, point sourceX high, point gate high,
        point gate translatedLow, point targetX translatedLow,
        point targetX (size.addConstant 3)]
  | .negativeVertical =>
      let translatedHigh := high.subtract size
      [sourcePoint, point sourceX low, point gate low,
        point gate translatedHigh, point targetX translatedHigh,
        point targetX ((constant 3).subtract size)]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
