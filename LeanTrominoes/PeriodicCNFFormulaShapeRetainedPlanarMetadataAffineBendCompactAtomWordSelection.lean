/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendBaseSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordSemantics

/-! # Exact affine selection of compact retained-bend atom words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open GuardedCarrierKeyCompactAtomWords

/-- A failed route-shape guard suppresses every compact-word block carrying
that guard. -/
theorem BendTemplate.compactAtomWordSelection_eq_nil_of_not_matches
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        ((template.compactAtomWordRecipeBlocks shape).map
          (recipeBlockWords (descriptorPairTokens pair)))
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    BendTemplate.compactAtomWordRecipeBlocks
  rw [List.map_map, List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  have guardFalse :
      (shape.guard .first).evalPair pair = false := by
    rw [shape.evalPair_guard]
    simp [notMatches, descriptorAt]
  have predicateFalse :
      ∀ ports,
        (template.descriptorPredicate shape ports).evalPair pair = false := by
    intro ports
    simp [BendTemplate.descriptorPredicate, evalPair_all, guardFalse]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun _ =>
          recipeBlockWords (descriptorPairTokens pair)
            template.compactAtomWordRecipes)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = []
  simp_rw [predicateFalse]
  simp [allCornerPortPairs, allCornerPorts, selectTruthBlocks]

/-- Different edge indices suppress every compact-word block for one bend
position. -/
theorem BendTemplate.compactAtomWordSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        ((template.compactAtomWordRecipeBlocks shape).map
          (recipeBlockWords (descriptorPairTokens pair)))
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    BendTemplate.compactAtomWordRecipeBlocks
  rw [List.map_map, List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  have diagonalFalse : sameEdgeIndexPredicate.evalPair pair = false := by
    rw [sameEdgeIndexPredicate_evalPair]
    simp [edgeIndexNe]
  have predicateFalse :
      ∀ ports,
        (template.descriptorPredicate shape ports).evalPair pair = false := by
    intro ports
    simp [BendTemplate.descriptorPredicate, evalPair_all, diagonalFalse]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun _ =>
          recipeBlockWords (descriptorPairTokens pair)
            template.compactAtomWordRecipes)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = []
  simp_rw [predicateFalse]
  simp [allCornerPortPairs, allCornerPorts, selectTruthBlocks]

/-- Under its guard, one route-shape scan emits exactly four compact
occurrence words per evaluated base bend. -/
theorem RouteShape.bendCompactAtomWordSelection_eq
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (incomingGenuine :
      ∀ template ∈ shape.baseBendTemplates,
        (AxisDirection.between
          (template.incomingStart.evalPair pair)
          (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      ∀ template ∈ shape.baseBendTemplates,
        (AxisDirection.between
          (template.bend.evalPair pair)
          (template.outgoingFinish.evalPair pair)).IsGenuine) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        (shape.bendCompactAtomWordRecipeBlocks.map
          (recipeBlockWords (descriptorPairTokens pair)))
        (descriptorPairTokens pair) =
      shape.baseBendTemplates.flatMap fun template =>
        (template.evalPair .first pair).compactAtomWords := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendCompactAtomWordRecipeBlocks
  rw [List.map_flatMap, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_congr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.descriptorPredicates_selectedCompactAtomWords
      shape pair sameEdge shapeMatches
      (incomingGenuine template templateMember)
      (outgoingGenuine template templateMember)
  · intro template _templateMember
    simp [BendTemplate.compactAtomWordRecipeBlocks]

/-- A nonmatching route shape contributes no compact bend words. -/
theorem RouteShape.bendCompactAtomWordSelection_eq_nil_of_not_matches
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        (shape.bendCompactAtomWordRecipeBlocks.map
          (recipeBlockWords (descriptorPairTokens pair)))
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendCompactAtomWordRecipeBlocks
  rw [List.map_flatMap, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.compactAtomWordSelection_eq_nil_of_not_matches
      shape pair notMatches
  · intro template _templateMember
    simp [BendTemplate.compactAtomWordRecipeBlocks]

/-- Different edge indices make one complete route-shape compact scan empty. -/
theorem RouteShape.bendCompactAtomWordSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        (shape.bendCompactAtomWordRecipeBlocks.map
          (recipeBlockWords (descriptorPairTokens pair)))
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendCompactAtomWordRecipeBlocks
  rw [List.map_flatMap, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.compactAtomWordSelection_eq_nil_of_edgeIndex_ne
      shape pair edgeIndexNe
  · intro template _templateMember
    simp [BendTemplate.compactAtomWordRecipeBlocks]

/-- The complete affine selector keeps the unique matching route shape and
emits exactly its evaluated base-bend compact words. -/
theorem bendCompactAtomWords_eq_of_matches
    (selectedShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : selectedShape.Matches pair.1)
    (incomingGenuine :
      ∀ template ∈ selectedShape.baseBendTemplates,
        (AxisDirection.between
          (template.incomingStart.evalPair pair)
          (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      ∀ template ∈ selectedShape.baseBendTemplates,
        (AxisDirection.between
          (template.bend.evalPair pair)
          (template.outgoingFinish.evalPair pair)).IsGenuine) :
    bendCompactAtomWords (descriptorPairTokens pair) =
      selectedShape.baseBendTemplates.flatMap fun template =>
        (template.evalPair .first pair).compactAtomWords := by
  rw [bendCompactAtomWords_eq_predicateListBlocks]
  unfold bendDescriptorPredicates bendCompactAtomWordRecipeBlocks
  rw [List.map_flatMap, predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · rw [flatMap_eq_of_unique
      allRouteShapes
      (fun shape =>
        selectTruthBlocks
          (shape.bendCompactAtomWordRecipeBlocks.map
            (recipeBlockWords (descriptorPairTokens pair)))
          (shape.bendDescriptorPredicates.map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair)))
      selectedShape allRouteShapes_nodup
      (mem_allRouteShapes selectedShape)]
    · rw [← predicateListBlocks_eq]
      exact selectedShape.bendCompactAtomWordSelection_eq pair sameEdge
        shapeMatches incomingGenuine outgoingGenuine
    · intro shape shapeMember shapeNe
      rw [← predicateListBlocks_eq]
      apply shape.bendCompactAtomWordSelection_eq_nil_of_not_matches
      intro otherMatches
      exact shapeNe (RouteShape.eq_of_matches otherMatches shapeMatches)
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendCompactAtomWordRecipeBlocks,
      BendTemplate.compactAtomWordRecipeBlocks]

/-- The complete affine compact bend selector is empty off the edge-index
diagonal. -/
theorem bendCompactAtomWords_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    bendCompactAtomWords (descriptorPairTokens pair) = [] := by
  rw [bendCompactAtomWords_eq_predicateListBlocks]
  unfold bendDescriptorPredicates bendCompactAtomWordRecipeBlocks
  rw [List.map_flatMap, predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape shapeMember
    rw [← predicateListBlocks_eq]
    exact shape.bendCompactAtomWordSelection_eq_nil_of_edgeIndex_ne
      pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendCompactAtomWordRecipeBlocks,
      BendTemplate.compactAtomWordRecipeBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
