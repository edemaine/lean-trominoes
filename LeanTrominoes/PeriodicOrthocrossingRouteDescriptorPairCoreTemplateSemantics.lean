/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebraSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCoreTemplates

/-! # Exact semantics of local affine descriptor core templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Every local core guard recognizes exactly its corresponding semantic
offset and port-order branch. -/
theorem CoreShape.evalPair_guard
    (shape : CoreShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.guard side).evalPair pair =
      decide (shape.Matches (descriptorAt pair side)) := by
  cases shape <;>
    simp [CoreShape.guard, CoreShape.Matches,
      evalPair_horizontalOffset,
      evalPair_verticalOffset, evalPair_sourcePortX, evalPair_targetPortX,
      Prod.ext_iff, and_assoc] <;>
    rw [← decide_not] <;>
    simp

/-- The same shape guard is exact when evaluated physically on the canonical
tagged pair block. -/
theorem CoreShape.evalTokens_guard
    (shape : CoreShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.guard side).evalTokens (descriptorPairTokens pair) =
      decide (shape.Matches (descriptorAt pair side)) := by
  rw [Predicate.evalTokens_descriptorPairTokens, shape.evalPair_guard]

/-- Under its semantic branch condition, each finite affine point template
evaluates to the exact point list returned by `RouteDescriptor.core`. -/
theorem CoreShape.map_evalPair_points
    (shape : CoreShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.points side).map (fun affinePoint => affinePoint.evalPair pair) =
      (descriptorAt pair side).core := by
  cases shape with
  | zero =>
      simp [CoreShape.points, RouteDescriptor.core,
        show (descriptorAt pair side).offset = (0, 0) from shapeMatches,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_lowTrack,
        Cell.add, Cell.scale]
  | positiveHorizontalDirect =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.points, RouteDescriptor.core, offset, order,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_gridSize,
        evalPair_lowTrack, Cell.add, Cell.scale]
      ring
  | positiveHorizontalBent =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.points, RouteDescriptor.core, offset, order,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_gridSize,
        evalPair_lowTrack, evalPair_highTrack, Cell.add, Cell.scale]
      ring
  | negativeHorizontalDirect =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.points, RouteDescriptor.core, offset, order,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_gridSize,
        evalPair_lowTrack, Cell.add, Cell.scale]
      ring
  | negativeHorizontalBent =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.points, RouteDescriptor.core, offset, order,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_gridSize,
        evalPair_lowTrack, evalPair_highTrack, Cell.add, Cell.scale]
      ring
  | positiveVertical =>
      simp [CoreShape.points, RouteDescriptor.core,
        show (descriptorAt pair side).offset = (0, 1) from shapeMatches,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_gridSize,
        evalPair_lowTrack, evalPair_highTrack, evalPair_gateX,
        Cell.add, Cell.scale]
      ring_nf
      simp
  | negativeVertical =>
      simp [CoreShape.points, RouteDescriptor.core,
        show (descriptorAt pair side).offset = (0, -1) from shapeMatches,
        evalPair_sourcePortX, evalPair_targetPortX, evalPair_gridSize,
        evalPair_lowTrack, evalPair_highTrack, evalPair_gateX,
        Cell.add, Cell.scale]
      ring_nf

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
