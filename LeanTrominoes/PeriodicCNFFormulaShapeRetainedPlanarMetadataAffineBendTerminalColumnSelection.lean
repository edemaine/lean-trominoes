/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendBaseSemantics

/-! # Generic affine selection of retained-bend port blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

/-- The sixteen port predicates select the output block belonging to the
evaluated genuine bend. -/
theorem BendTemplate.descriptorPredicates_selectedPortBlock
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
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
        (bendTemplatePortBlocks block)
        (descriptorPairTokens pair) =
      block
        (template.evalPair .first pair).incomingPort
        (template.evalPair .first pair).outgoingPort := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates bendTemplatePortBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports => block ports.1 ports.2)
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

/-- A failed route-shape guard suppresses every aligned port block. -/
theorem BendTemplate.portBlockSelection_eq_nil_of_not_matches
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        (bendTemplatePortBlocks block)
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates bendTemplatePortBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports => block ports.1 ports.2)
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

/-- Under its guard, one route-shape scan emits precisely one output block
per evaluated base bend. -/
theorem RouteShape.bendPortBlockSelection_eq
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
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
        (shape.bendPortBlocks block)
        (descriptorPairTokens pair) =
      shape.baseBendTemplates.flatMap fun template =>
        block
          (template.evalPair .first pair).incomingPort
          (template.evalPair .first pair).outgoingPort := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates RouteShape.bendPortBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_congr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.descriptorPredicates_selectedPortBlock block shape pair
      sameEdge shapeMatches
      (incomingGenuine template templateMember)
      (outgoingGenuine template templateMember)
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates, bendTemplatePortBlocks]

/-- A nonmatching route shape contributes no port blocks. -/
theorem RouteShape.bendPortBlockSelection_eq_nil_of_not_matches
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        (shape.bendPortBlocks block)
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates RouteShape.bendPortBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.portBlockSelection_eq_nil_of_not_matches
      block shape pair notMatches
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates, bendTemplatePortBlocks]

/-- The complete affine selector retains the unique matching route shape. -/
theorem affineBaseBendPortBlock_eq_of_matches
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
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
    affineBaseBendPortBlock block (descriptorPairTokens pair) =
      selectedShape.baseBendTemplates.flatMap fun template =>
        block
          (template.evalPair .first pair).incomingPort
          (template.evalPair .first pair).outgoingPort := by
  unfold affineBaseBendPortBlock bendDescriptorPredicates
  rw [predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · rw [flatMap_eq_of_unique allRouteShapes
      (fun shape =>
        selectTruthBlocks (shape.bendPortBlocks block)
          (shape.bendDescriptorPredicates.map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair)))
      selectedShape allRouteShapes_nodup
      (mem_allRouteShapes selectedShape)]
    · rw [← predicateListBlocks_eq]
      exact selectedShape.bendPortBlockSelection_eq block pair sameEdge
        shapeMatches incomingGenuine outgoingGenuine
    · intro shape _shapeMember shapeNe
      rw [← predicateListBlocks_eq]
      apply shape.bendPortBlockSelection_eq_nil_of_not_matches block pair
      intro otherMatches
      exact shapeNe (RouteShape.eq_of_matches otherMatches shapeMatches)
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates, RouteShape.bendPortBlocks,
      BendTemplate.descriptorPredicates, bendTemplatePortBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

