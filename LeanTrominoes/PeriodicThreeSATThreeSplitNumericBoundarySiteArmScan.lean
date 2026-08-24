/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericSiteArmScanData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorPositiveRank
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections

/-! # Boundary site-arm blocks of the split descriptor stream -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The numeric boundary arm scan of split descriptors emits one three-site
block for each positive-offset copied occurrence, in occurrence order. -/
theorem splitRouteDescriptors_numericBoundarySiteArmBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (splitRouteDescriptors source).flatMap
        routedVariableBoundarySiteArmBlocks =
      (occurrenceRouteDescriptors source).flatMap fun descriptor =>
        if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundarySiteArmBlocks else [] := by
  unfold splitRouteDescriptors
  rw [List.flatMap_append]
  have prefixEq :
      (occurrenceRouteDescriptors source).flatMap
          routedVariableBoundarySiteArmBlocks =
        (occurrenceRouteDescriptors source).flatMap fun descriptor =>
          if descriptor.offset = ((1, 0) : Cell) then
            routedVariableNextBoundarySiteArmBlocks else [] := by
    apply List.flatMap_congr
    intro descriptor descriptorMember
    unfold routedVariableBoundarySiteArmBlocks
    have rankZero := occurrenceRouteDescriptor_targetPortRank_eq_zero
      source descriptorMember
    simp [rankZero]
  have suffixEq :
      (cycleLinkRouteDescriptors source).flatMap
          routedVariableBoundarySiteArmBlocks = [] := by
    calc
      _ = (cycleLinkRouteDescriptors source).flatMap (fun _ => []) := by
          apply List.flatMap_congr
          intro descriptor descriptorMember
          unfold routedVariableBoundarySiteArmBlocks
          have positive := cycleLinkRouteDescriptor_targetPortRank_ne_zero
            source descriptorMember
          simp [positive]
      _ = [] := by simp
  rw [prefixEq, suffixEq, List.append_nil]

end LeanTrominoes.PeriodicThreeSATThree
