/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendBaseSemantics

/-! # Exact finite selection of retained-bend route source prefixes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The sixteen port predicates select exactly the source-prefix block of
the evaluated bend. -/
theorem BendTemplate.descriptorPredicates_selectedRoutePrefixDirectionBlock
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (incomingGenuine :
      (AxisDirection.between
        (template.incomingStart.evalPair pair)
        (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      (AxisDirection.between
        (template.bend.evalPair pair)
        (template.outgoingFinish.evalPair pair)).IsGenuine) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateRoutePrefixDirectionBlocks
        (descriptorPairTokens pair) =
      canonicalBendRoutePrefixDirectionBlock
        (template.evalPair .first pair).incomingPort
        (template.evalPair .first pair).outgoingPort := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    bendTemplateRoutePrefixDirectionBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports =>
          canonicalBendRoutePrefixDirectionBlock ports.1 ports.2)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = _
  simp_rw [BendTemplate.descriptorPredicate_evalPair shape template _ pair
    sameEdge shapeMatches incomingGenuine outgoingGenuine]
  generalize incomingEq :
      (template.evalPair .first pair).incomingPort = incoming
  generalize outgoingEq :
      (template.evalPair .first pair).outgoingPort = outgoing
  cases incoming <;> cases outgoing <;>
    simp [allCornerPortPairs, allCornerPorts, selectTruthBlocks]

/-- A failed route-shape guard suppresses every source-prefix block carrying
that guard. -/
theorem BendTemplate.routePrefixDirectionSelection_eq_nil_of_not_matches
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateRoutePrefixDirectionBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    bendTemplateRoutePrefixDirectionBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports =>
          canonicalBendRoutePrefixDirectionBlock ports.1 ports.2)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = []
  have guardFalse :
      (shape.guard .first).evalPair pair = false := by
    rw [shape.evalPair_guard]
    simp [notMatches, descriptorAt]
  have predicateFalse :
      ∀ ports,
        (template.descriptorPredicate shape ports).evalPair pair = false := by
    intro ports
    simp [BendTemplate.descriptorPredicate, evalPair_all, guardFalse]
  simp [allCornerPortPairs, allCornerPorts,
    selectTruthBlocks, predicateFalse]

/-- Under its guard, one route-shape scan emits one delimited four-prefix
block per evaluated base bend. -/
theorem RouteShape.bendRoutePrefixDirectionSelection_eq
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
        shape.bendRoutePrefixDirectionBlocks
        (descriptorPairTokens pair) =
      shape.baseBendTemplates.flatMap fun template =>
        canonicalBendRoutePrefixDirectionBlock
          (template.evalPair .first pair).incomingPort
          (template.evalPair .first pair).outgoingPort := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendRoutePrefixDirectionBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_congr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.descriptorPredicates_selectedRoutePrefixDirectionBlock
      shape pair sameEdge shapeMatches
      (incomingGenuine template templateMember)
      (outgoingGenuine template templateMember)
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateRoutePrefixDirectionBlocks]

/-- A nonmatching route shape contributes no bend source prefixes. -/
theorem RouteShape.bendRoutePrefixDirectionSelection_eq_nil_of_not_matches
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendRoutePrefixDirectionBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendRoutePrefixDirectionBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.routePrefixDirectionSelection_eq_nil_of_not_matches
      shape pair notMatches
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateRoutePrefixDirectionBlocks]

/-- The complete affine selector keeps the unique matching route shape and
returns exactly its evaluated base-bend source prefixes. -/
theorem affineBaseBendRoutePrefixDirectionBlock_eq_of_matches
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
    affineBaseBendRoutePrefixDirectionBlock (descriptorPairTokens pair) =
      selectedShape.baseBendTemplates.flatMap fun template =>
        canonicalBendRoutePrefixDirectionBlock
          (template.evalPair .first pair).incomingPort
          (template.evalPair .first pair).outgoingPort := by
  unfold affineBaseBendRoutePrefixDirectionBlock bendDescriptorPredicates
  rw [predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · rw [flatMap_eq_of_unique
      allRouteShapes
      (fun shape =>
        selectTruthBlocks shape.bendRoutePrefixDirectionBlocks
          (shape.bendDescriptorPredicates.map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair)))
      selectedShape allRouteShapes_nodup
      (mem_allRouteShapes selectedShape)]
    · rw [← predicateListBlocks_eq]
      exact selectedShape.bendRoutePrefixDirectionSelection_eq pair sameEdge
        shapeMatches incomingGenuine outgoingGenuine
    · intro shape _shapeMember shapeNe
      rw [← predicateListBlocks_eq]
      apply shape.bendRoutePrefixDirectionSelection_eq_nil_of_not_matches
      intro otherMatches
      exact shapeNe
        (RouteShape.eq_of_matches otherMatches shapeMatches)
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendRoutePrefixDirectionBlocks,
      BendTemplate.descriptorPredicates,
      bendTemplateRoutePrefixDirectionBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
