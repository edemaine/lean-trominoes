/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFindBool
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericSiteArmScanData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorPositiveRank
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCycleTargetBlockData

/-! # Rank-zero target lookup in the split route-descriptor stream -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Rank-zero lookup in the full split stream is exactly target lookup in the
copied-occurrence prefix; cycle descriptors all have positive target rank. -/
theorem occurrenceDescriptorAtTargetIndex_splitRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (targetIndex : Nat) :
    occurrenceDescriptorAtTargetIndex
        (splitRouteDescriptors source) targetIndex =
      occurrenceRouteDescriptorAtTargetIndex source targetIndex := by
  unfold occurrenceDescriptorAtTargetIndex
    occurrenceRouteDescriptorAtTargetIndex splitRouteDescriptors
  let fullPredicate := fun descriptor : RouteDescriptor =>
    decide (descriptor.targetPortRank = 0 ∧
      descriptor.targetVertexIndex = targetIndex)
  let targetPredicate := fun descriptor : RouteDescriptor =>
    decide (descriptor.targetVertexIndex = targetIndex)
  calc
    (occurrenceRouteDescriptors source ++
          cycleLinkRouteDescriptors source).find? fullPredicate =
        (occurrenceRouteDescriptors source).find? fullPredicate := by
      apply listFind?_append_of_right_forall_false
      intro descriptor descriptorMember
      have positive := cycleLinkRouteDescriptor_targetPortRank_ne_zero
        source descriptorMember
      simp [fullPredicate, positive]
    _ = (occurrenceRouteDescriptors source).find? targetPredicate := by
      apply listFind?_congr_of_forall_mem
      intro descriptor descriptorMember
      have rankZero := occurrenceRouteDescriptor_targetPortRank_eq_zero
        source descriptorMember
      simp [fullPredicate, targetPredicate, rankZero]

end LeanTrominoes.PeriodicThreeSATThree
