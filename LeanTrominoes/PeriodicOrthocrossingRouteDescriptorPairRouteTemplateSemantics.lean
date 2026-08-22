/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteTemplateTranslation
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics

/-! # Exact semantics of complete local affine descriptor routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Each endpoint fanout guard is exact on semantic descriptor fields. -/
theorem FanoutShape.evalPair_guard
    (shape : FanoutShape) (endpoint : Endpoint) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.guard endpoint side).evalPair pair =
      decide (shape.Matches endpoint (descriptorAt pair side)) := by
  cases shape <;> cases endpoint <;>
    simp [FanoutShape.guard, FanoutShape.Matches, Endpoint.centerX,
      Endpoint.portX, evalPair_sourceCenterX, evalPair_targetCenterX,
      evalPair_sourcePortX, evalPair_targetPortX]

/-- The same endpoint fanout guard is exact on a canonical tagged pair block. -/
theorem FanoutShape.evalTokens_guard
    (shape : FanoutShape) (endpoint : Endpoint) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.guard endpoint side).evalTokens (descriptorPairTokens pair) =
      decide (shape.Matches endpoint (descriptorAt pair side)) := by
  rw [Predicate.evalTokens_descriptorPairTokens, shape.evalPair_guard]

/-- A selected source fanout template evaluates to the semantic source
fanout exactly. -/
theorem FanoutShape.map_evalPair_sourcePoints
    (shape : FanoutShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches .source (descriptorAt pair side)) :
    (shape.sourcePoints side).map
        (fun affinePoint => affinePoint.evalPair pair) =
      fanout (vertexX (descriptorAt pair side).sourceVertexIndex)
        (descriptorPortX (descriptorAt pair side).sourceVertexIndex
          (descriptorAt pair side).sourcePortRank) := by
  cases shape with
  | straight =>
      simp [FanoutShape.Matches] at shapeMatches
      simp [FanoutShape.sourcePoints, fanout, shapeMatches,
        evalPair_sourceCenterX, evalPair_sourcePortX]
  | bent =>
      simp [FanoutShape.Matches] at shapeMatches
      simp [FanoutShape.sourcePoints, fanout, shapeMatches,
        evalPair_sourceCenterX, evalPair_sourcePortX]

/-- A selected target-tail template evaluates to the tail of the translated,
reversed semantic target fanout exactly. -/
theorem FanoutShape.map_evalPair_targetTail
    (shape : FanoutShape) (coreShape : CoreShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (fanoutMatches : shape.Matches .target (descriptorAt pair side))
    (coreMatches : coreShape.Matches (descriptorAt pair side)) :
    (shape.targetTail coreShape side).map
        (fun affinePoint => affinePoint.evalPair pair) =
      (translatePolyline
        (Cell.scale ((descriptorAt pair side).gridSize : Int)
          (descriptorAt pair side).offset)
        (fanout (vertexX (descriptorAt pair side).targetVertexIndex)
          (descriptorPortX (descriptorAt pair side).targetVertexIndex
            (descriptorAt pair side).targetPortRank)).reverse).tail := by
  cases shape with
  | straight =>
      simp [FanoutShape.Matches] at fanoutMatches
      simp [FanoutShape.targetTail, fanout, fanoutMatches,
        translatePolyline, evalPair_targetCenterX,
        coreShape.evalPair_translatePoint side pair _ coreMatches,
        Cell.add, add_comm]
  | bent =>
      simp [FanoutShape.Matches] at fanoutMatches
      simp [FanoutShape.targetTail, fanout, fanoutMatches,
        translatePolyline, evalPair_targetCenterX, evalPair_targetPortX,
        coreShape.evalPair_translatePoint side pair _ coreMatches,
        Cell.add, add_comm]

/-- The three selected finite affine templates assemble to the exact complete
semantic descriptor route. -/
theorem map_evalPair_routePoints
    (sourceShape : FanoutShape) (coreShape : CoreShape)
    (targetShape : FanoutShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (sourceMatches : sourceShape.Matches .source (descriptorAt pair side))
    (coreMatches : coreShape.Matches (descriptorAt pair side))
    (targetMatches : targetShape.Matches .target (descriptorAt pair side)) :
    (routePoints sourceShape coreShape targetShape side).map
        (fun affinePoint => affinePoint.evalPair pair) =
      (descriptorAt pair side).route := by
  unfold routePoints RouteDescriptor.route joinPolylines
  simp only [List.map_append, List.map_tail]
  rw [sourceShape.map_evalPair_sourcePoints side pair sourceMatches,
    coreShape.map_evalPair_points side pair coreMatches,
    targetShape.map_evalPair_targetTail coreShape side pair
      targetMatches coreMatches]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
