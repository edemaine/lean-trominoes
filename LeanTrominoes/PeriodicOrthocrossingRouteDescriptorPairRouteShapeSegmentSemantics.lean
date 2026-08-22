/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSegmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegments
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteTemplateSemantics

/-! # Exact semantics of finite affine route-shape segments -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The combined route-shape guard recognizes exactly its three semantic
shape conditions. -/
theorem RouteShape.evalPair_guard
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.guard side).evalPair pair =
      decide (shape.Matches (descriptorAt pair side)) := by
  rcases shape with ⟨source, core, target⟩
  simp [RouteShape.guard, RouteShape.Matches,
    FanoutShape.evalPair_guard, CoreShape.evalPair_guard]

/-- The same combined route-shape guard is exact on canonical tagged input. -/
theorem RouteShape.evalTokens_guard
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.guard side).evalTokens (descriptorPairTokens pair) =
      decide (shape.Matches (descriptorAt pair side)) := by
  rw [Predicate.evalTokens_descriptorPairTokens, shape.evalPair_guard]

/-- Under its combined semantic guard, a route shape evaluates to the exact
complete descriptor route. -/
theorem RouteShape.map_evalPair_points
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.points side).map (fun affinePoint => affinePoint.evalPair pair) =
      (descriptorAt pair side).route := by
  rcases shape with ⟨source, core, target⟩
  rcases shapeMatches with ⟨sourceMatches, coreMatches, targetMatches⟩
  exact map_evalPair_routePoints source core target side pair
    sourceMatches coreMatches targetMatches

/-- Consecutive segments of a selected affine route shape evaluate to the
exact semantic descriptor segments. -/
theorem RouteShape.map_evalPair_segments
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.segments side).map (fun segment => segment.evalPair pair) =
      gridPolylineSegments (descriptorAt pair side).route := by
  have pointsEq :
      (shape.points side).map (Point.eval (pairFieldValue pair)) =
        (descriptorAt pair side).route :=
    shape.map_evalPair_points side pair shapeMatches
  unfold RouteShape.segments Segment.evalPair
  rw [map_eval_segments]
  rw [pointsEq]

/-- Every finite affine route shape has at most nine segment templates. -/
theorem RouteShape.segments_length_le_nine
    (shape : RouteShape) (side : Side) :
    (shape.segments side).length ≤ 9 := by
  rcases shape with ⟨source, core, target⟩
  cases source <;> cases core <;> cases target <;> cases side <;>
    decide

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
