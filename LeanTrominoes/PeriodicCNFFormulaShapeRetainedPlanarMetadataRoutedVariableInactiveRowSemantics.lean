/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData

/-! # Inactive rows of the routed-variable pair scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A descriptor whose target rank is neither zero nor two cannot be the
first member of any selected routed-variable pair. -/
theorem routedVariablePairDescriptorRow_eq_nil_of_rank_ne_zero_two
    (descriptors : List RouteDescriptor)
    (first : RouteDescriptor)
    (rankNeZero : first.targetPortRank ≠ 0)
    (rankNeTwo : first.targetPortRank ≠ 2) :
    descriptors.flatMap (fun second =>
      routedVariablePairDescriptorBlock (first, second)) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro second _secondMember
  simp [routedVariablePairDescriptorBlock,
    routedVariableNextBoundaryPair,
    routedVariableCurrentCyclePair,
    routedVariableNextCyclePair, rankNeZero, rankNeTwo]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
