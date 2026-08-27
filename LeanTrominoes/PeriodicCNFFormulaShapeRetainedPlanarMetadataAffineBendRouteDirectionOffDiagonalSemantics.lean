/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionSelection
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendOffDiagonalSemantics

/-! # Off-diagonal suppression of retained-bend route words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

/-- Different stored edge indices make every route-word predicate for one
bend false. -/
theorem BendTemplate.routeDirectionSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateRouteDirectionBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    bendTemplateRouteDirectionBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports =>
          canonicalBendRouteDirectionBlock ports.1 ports.2)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = []
  have diagonalFalse : sameEdgeIndexPredicate.evalPair pair = false := by
    rw [sameEdgeIndexPredicate_evalPair]
    simp [edgeIndexNe]
  have predicateFalse :
      ∀ ports,
        (template.descriptorPredicate shape ports).evalPair pair = false := by
    intro ports
    simp [BendTemplate.descriptorPredicate, evalPair_all, diagonalFalse]
  simp [allCornerPortPairs, allCornerPorts,
    selectTruthBlocks, predicateFalse]

/-- An off-diagonal pair contributes no bend words for one route shape. -/
theorem RouteShape.bendRouteDirectionSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendRouteDirectionBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendRouteDirectionBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.routeDirectionSelection_eq_nil_of_edgeIndex_ne
      shape pair edgeIndexNe
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateRouteDirectionBlocks]

/-- The complete bend route-word selector is empty off the edge-index
diagonal. -/
theorem affineBaseBendRouteDirectionBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineBaseBendRouteDirectionBlock (descriptorPairTokens pair) = [] := by
  unfold affineBaseBendRouteDirectionBlock bendDescriptorPredicates
  rw [predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape shapeMember
    rw [← predicateListBlocks_eq]
    exact shape.bendRouteDirectionSelection_eq_nil_of_edgeIndex_ne
      pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendRouteDirectionBlocks,
      BendTemplate.descriptorPredicates,
      bendTemplateRouteDirectionBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
