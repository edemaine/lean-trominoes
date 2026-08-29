/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendOffDiagonalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionScalingCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics

/-! # Stream semantics of scaled retained-bend source prefixes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine
namespace BendRoutePrefixDirectionScaling

open PlanarThreeSAT RouteDescriptorPairFieldTags

theorem BendTemplate.routePrefixDirectionSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateRoutePrefixDirectionBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    bendTemplateRoutePrefixDirectionBlocks
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

theorem RouteShape.bendRoutePrefixDirectionSelection_eq_nil_of_edgeIndex_ne
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendRoutePrefixDirectionBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendRoutePrefixDirectionBlocks
  rw [List.map_flatMap, selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact BendTemplate.routePrefixDirectionSelection_eq_nil_of_edgeIndex_ne
      shape template pair edgeIndexNe
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateRoutePrefixDirectionBlocks]

private theorem affineBaseBendRoutePrefixDirectionBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    affineBaseBendRoutePrefixDirectionBlock
        (descriptorPairTokens pair) = [] := by
  unfold affineBaseBendRoutePrefixDirectionBlock bendDescriptorPredicates
  rw [predicateListBlocks_eq, List.map_flatMap,
    selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape shapeMember
    rw [← predicateListBlocks_eq]
    exact RouteShape.bendRoutePrefixDirectionSelection_eq_nil_of_edgeIndex_ne
      shape pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendRoutePrefixDirectionBlocks,
      BendTemplate.descriptorPredicates,
      bendTemplateRoutePrefixDirectionBlocks]

private theorem blockOutput_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    blockOutput (descriptorPairTokens pair) = [] := by
  unfold blockOutput
  rw [affineBaseBendRoutePrefixDirectionBlock_eq_nil_of_edgeIndex_ne
    pair edgeIndexNe]
  rfl

@[simp] theorem streamOutput_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    streamOutput (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        blockOutput (descriptorPairTokens pair) := by
  unfold streamOutput
  rw [affineBaseBendRoutePrefixDirectionStream,
    mappedOutput_encodeDescriptorPairs]
  exact
    PeriodicEightOccurrenceSplit.FallbackPrefixDirectionScaling.output_flatMap
      _ _

/-- On numeric source routes, scaled affine prefix selection emits exactly
four scaled source-prefix words for every untranslated semantic bend. -/
theorem streamOutput_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    streamOutput
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            canonicalScaledBendRoutePrefixDirectionBlock
              routeBend.incomingPort routeBend.outgoingPort := by
  rw [streamOutput_encodeDescriptorPairs]
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair => blockOutput (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
        formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact blockOutput_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact blockOutput_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end BendRoutePrefixDirectionScaling
end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
