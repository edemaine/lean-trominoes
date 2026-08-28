/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics

/-! # Alignment of affine bend predicates and compact-word recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem BendTemplate.compactAtomWordRecipeBlocks_length
    (template : BendTemplate) (shape : RouteShape) :
    (template.compactAtomWordRecipeBlocks shape).length =
      (template.descriptorPredicates shape).length := by
  simp [BendTemplate.compactAtomWordRecipeBlocks]

@[simp] theorem RouteShape.bendCompactAtomWordRecipeBlocks_length
    (shape : RouteShape) :
    shape.bendCompactAtomWordRecipeBlocks.length =
      shape.bendDescriptorPredicates.length := by
  unfold RouteShape.bendCompactAtomWordRecipeBlocks
    RouteShape.bendDescriptorPredicates
  simp

@[simp] theorem bendCompactAtomWordRecipeBlocks_length :
    bendCompactAtomWordRecipeBlocks.length =
      bendDescriptorPredicates.length := by
  unfold bendCompactAtomWordRecipeBlocks bendDescriptorPredicates
  simp

/-- Compiled bend activity is exactly the semantic predicate truth word
expanded over its aligned four-recipe blocks. -/
@[simp] theorem bendCompactAtomWordExpandedActives_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    bendCompactAtomWordExpandedActives tokens =
      expandedActives
        (bendDescriptorPredicates.map fun predicate =>
          predicate.evalTokens tokens)
        bendCompactAtomWordRecipeBlocks := by
  unfold bendCompactAtomWordExpandedActives predicateListExpandedActives
  rw [predicateListTruthValues_eq]
  apply compiledExpandedActives_eq
  rw [List.length_map]
  exact bendCompactAtomWordRecipeBlocks_length.symm

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
