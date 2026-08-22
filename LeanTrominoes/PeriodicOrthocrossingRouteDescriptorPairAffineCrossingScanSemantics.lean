/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListUniqueSum
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScanLocalSemantics

/-! # Exact semantics of the complete finite affine crossing scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- A route-shape pair whose two semantic guards do not both hold contributes
zero to the finite affine scan. -/
theorem guardedRouteShapePairCrossingCount_eq_zero_of_not_matches
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬(shapes.1.Matches pair.1 ∧ shapes.2.Matches pair.2)) :
    guardedRouteShapePairCrossingCount
        (descriptorPairTokens pair) shapes = 0 := by
  unfold guardedRouteShapePairCrossingCount
  rw [if_neg]
  intro enabled
  exact notMatches
    ((routeShapePairEnabled_descriptorPairTokens shapes pair).1 enabled)

/-- If two explicitly selected shapes match the two descriptors, the complete
twenty-eight-squared guarded scan reduces to that unique shape pair. -/
theorem affineCrossingCount_descriptorPairTokens_of_matches
    (firstShape secondShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : firstShape.Matches pair.1)
    (secondMatches : secondShape.Matches pair.2) :
    affineCrossingCount (descriptorPairTokens pair) =
      routeDescriptorPairLinearCrossingCountAtPeriod pair.1.gridSize pair := by
  unfold affineCrossingCount
  rw [List.sum_map_eq_of_unique
    (guardedRouteShapePairCrossingCount (descriptorPairTokens pair))
    (allRouteShapes ×ˢ allRouteShapes) (firstShape, secondShape)
    (allRouteShapes_nodup.product allRouteShapes_nodup)
    (List.mem_product.mpr ⟨mem_allRouteShapes firstShape,
      mem_allRouteShapes secondShape⟩)]
  · exact guardedRouteShapePairCrossingCount_descriptorPairTokens
      (firstShape, secondShape) pair firstMatches secondMatches
  · intro shapes shapesMember shapesNe
    apply guardedRouteShapePairCrossingCount_eq_zero_of_not_matches
    intro shapeMatches
    apply shapesNe
    apply Prod.ext
    · exact RouteShape.eq_of_matches shapeMatches.1 firstMatches
    · exact RouteShape.eq_of_matches shapeMatches.2 secondMatches

/-- On any pair of locally shaped descriptors, the fixed tagged-token scan
equals the canonical pair-local linear crossing count. -/
theorem affineCrossingCount_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor)
    (firstLocal :
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape pair.1)
    (secondLocal :
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape pair.2) :
    affineCrossingCount (descriptorPairTokens pair) =
      routeDescriptorPairLinearCrossingCountAtPeriod pair.1.gridSize pair := by
  rcases firstLocal with ⟨firstShape, firstMatches⟩
  rcases secondLocal with ⟨secondShape, secondMatches⟩
  exact affineCrossingCount_descriptorPairTokens_of_matches
    firstShape secondShape pair firstMatches secondMatches

/-- The finite affine scan emits exactly the canonical self-period crossing
marker block for every locally shaped descriptor pair. -/
theorem affineCrossingMarkers_descriptorPairTokens
    (marker : α) (pair : RouteDescriptor × RouteDescriptor)
    (firstLocal :
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape pair.1)
    (secondLocal :
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape pair.2) :
    affineCrossingMarkers marker (descriptorPairTokens pair) =
      routeDescriptorPairCrossingMarkers marker pair := by
  unfold affineCrossingMarkers routeDescriptorPairCrossingMarkers
  rw [affineCrossingCount_descriptorPairTokens pair firstLocal secondLocal]
  exact (routeDescriptorPairCrossingMarkersAtPeriod_eq_linear
    marker pair.1.gridSize pair).symm

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
