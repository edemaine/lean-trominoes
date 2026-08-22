/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendBaseSemantics

/-! # Off-diagonal semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

/-- Different stored edge indices make every predicate for one bend false. -/
theorem BendTemplate.descriptorPredicates_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateDescriptorBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates bendTemplateDescriptorBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports =>
          PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.canonicalBendDescriptorBlock
            ports.1 ports.2 false)
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

/-- Different stored edge indices make one complete route-shape scan empty. -/
theorem RouteShape.bendDescriptorSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendDescriptorBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendDescriptorBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.descriptorPredicates_eq_nil_of_edgeIndex_ne
      shape pair edgeIndexNe
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateDescriptorBlocks]

/-- The complete base selector is empty off the edge-index diagonal. -/
theorem affineBaseBendDescriptorBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineBaseBendDescriptorBlock (descriptorPairTokens pair) = [] := by
  unfold affineBaseBendDescriptorBlock bendDescriptorPredicates
    bendDescriptorBlocks
  rw [predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape shapeMember
    rw [← predicateListBlocks_eq]
    exact shape.bendDescriptorSelection_eq_nil_of_edgeIndex_ne
      pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendDescriptorBlocks,
      BendTemplate.descriptorPredicates,
      bendTemplateDescriptorBlocks]

/-- Repeating an empty base selector leaves the complete pair block empty. -/
theorem affineBendDescriptorBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineBendDescriptorBlock (descriptorPairTokens pair) = [] := by
  unfold affineBendDescriptorBlock
  rw [affineBaseBendDescriptorBlock_eq_nil_of_edgeIndex_ne pair edgeIndexNe]
  simp [repeatNeighborBendDescriptorBlock]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
