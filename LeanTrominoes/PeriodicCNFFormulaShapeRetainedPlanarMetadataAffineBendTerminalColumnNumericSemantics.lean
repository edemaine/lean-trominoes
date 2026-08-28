/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnSelection
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendNumericSemantics

/-! # Numeric semantics of retained-bend terminal-column selection -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

/-- On a numeric route's diagonal pair, the generic selector emits one
port-pair block per semantic untranslated bend. -/
theorem affineBaseBendPortBlock_numeric_diagonal
    {Variable Output : Type} [DecidableEq Variable]
    (block : CornerPort → CornerPort → List Output)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (shape : RouteShape)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula)
    (shapeMatches : shape.Matches descriptor) :
    affineBaseBendPortBlock block
        (descriptorPairTokens (descriptor, descriptor)) =
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          block routeBend.incomingPort routeBend.outgoingPort := by
  rw [affineBaseBendPortBlock_eq_of_matches
    block shape (descriptor, descriptor) rfl shapeMatches]
  · rw [← shape.map_evalPair_baseBendTemplates
      (descriptor, descriptor) shapeMatches,
      List.flatMap_map]
  · intro template templateMember
    exact (shape.baseBendTemplate_directionsGenuine
      formula wellFormed degree isLocal descriptor descriptorMember
      shapeMatches templateMember).1
  · intro template templateMember
    exact (shape.baseBendTemplate_directionsGenuine
      formula wellFormed degree isLocal descriptor descriptorMember
      shapeMatches templateMember).2

/-- An off-diagonal descriptor pair suppresses one template's arbitrary
port blocks. -/
theorem BendTemplate.portBlockSelection_eq_nil_of_edgeIndex_ne
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
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

/-- An off-diagonal descriptor pair suppresses one route shape's arbitrary
port blocks. -/
theorem RouteShape.bendPortBlockSelection_eq_nil_of_edgeIndex_ne
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
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
    exact template.portBlockSelection_eq_nil_of_edgeIndex_ne
      block shape pair edgeIndexNe
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates, bendTemplatePortBlocks]

/-- The complete generic bend selector is empty off the edge-index
diagonal. -/
theorem affineBaseBendPortBlock_eq_nil_of_edgeIndex_ne
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineBaseBendPortBlock block (descriptorPairTokens pair) = [] := by
  unfold affineBaseBendPortBlock bendDescriptorPredicates
  rw [predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape shapeMember
    rw [← predicateListBlocks_eq]
    exact shape.bendPortBlockSelection_eq_nil_of_edgeIndex_ne
      block pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates, RouteShape.bendPortBlocks,
      BendTemplate.descriptorPredicates, bendTemplatePortBlocks]

@[simp] theorem affineBaseBendTerminalDirectionBlock_eq_portBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    affineBaseBendTerminalDirectionBlock tokens =
      affineBaseBendPortBlock canonicalBendTerminalDirectionBlock tokens := by
  rfl

@[simp] theorem affineBaseBendTerminalRadialBlock_eq_portBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    affineBaseBendTerminalRadialBlock tokens =
      affineBaseBendPortBlock canonicalBendTerminalRadialBlock tokens := by
  rfl

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

