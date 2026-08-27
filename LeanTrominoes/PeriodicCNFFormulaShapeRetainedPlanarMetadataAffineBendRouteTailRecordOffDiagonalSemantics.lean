/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendOffDiagonalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordSelection

/-! # Off-diagonal suppression of retained-bend Figure 9 records -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

theorem BendTemplate.routeTailRecordSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateRouteTailRecordBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    bendTemplateRouteTailRecordBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
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

theorem RouteShape.bendRouteTailRecordSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendRouteTailRecordBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendRouteTailRecordBlocks
  rw [List.map_flatMap, selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.routeTailRecordSelection_eq_nil_of_edgeIndex_ne
      shape pair edgeIndexNe
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateRouteTailRecordBlocks]

theorem affineBaseBendRouteTailRecordBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineBaseBendRouteTailRecordBlock (descriptorPairTokens pair) = [] := by
  unfold affineBaseBendRouteTailRecordBlock bendDescriptorPredicates
  rw [predicateListBlocks_eq, List.map_flatMap,
    selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape shapeMember
    rw [← predicateListBlocks_eq]
    exact shape.bendRouteTailRecordSelection_eq_nil_of_edgeIndex_ne
      pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendRouteTailRecordBlocks,
      BendTemplate.descriptorPredicates,
      bendTemplateRouteTailRecordBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
