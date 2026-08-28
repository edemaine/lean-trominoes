/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics

/-! # Alignment of routed-variable predicates and word recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem RouteShape.routedVariableCompactAtomWordRecipeBlocks_length
    (shape : RouteShape) :
    shape.routedVariableCompactAtomWordRecipeBlocks.length =
      shape.routedVariableCompactAtomWordPredicates.length := by
  simp [RouteShape.routedVariableCompactAtomWordRecipeBlocks,
    RouteShape.routedVariableCompactAtomWordPredicates]

@[simp] theorem routedVariableCompactAtomWordRecipeBlocks_length :
    routedVariableCompactAtomWordRecipeBlocks.length =
      routedVariableCompactAtomWordPredicates.length := by
  unfold routedVariableCompactAtomWordRecipeBlocks
    routedVariableCompactAtomWordPredicates
  simp

/-- Compiled activity is the semantic predicate truth word expanded over
the aligned four-recipe blocks. -/
@[simp] theorem routedVariableCompactAtomWordExpandedActives_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    routedVariableCompactAtomWordExpandedActives tokens =
      expandedActives
        (routedVariableCompactAtomWordPredicates.map fun predicate =>
          predicate.evalTokens tokens)
        routedVariableCompactAtomWordRecipeBlocks := by
  unfold routedVariableCompactAtomWordExpandedActives
    predicateListExpandedActives
  rw [predicateListTruthValues_eq]
  apply compiledExpandedActives_eq
  rw [List.length_map]
  exact routedVariableCompactAtomWordRecipeBlocks_length.symm

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
