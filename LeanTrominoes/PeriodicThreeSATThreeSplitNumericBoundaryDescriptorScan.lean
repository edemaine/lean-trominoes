/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericDescriptorScanData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorPositiveRank
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections

/-! # Boundary descriptor blocks of the split route stream -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The numeric boundary scan of split descriptors emits exactly one block
for each positive-offset copied occurrence, in occurrence order. -/
theorem splitRouteDescriptors_numericBoundaryDescriptorBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (splitRouteDescriptors source).flatMap
        routedVariableNumericBoundaryDescriptorBlock =
      (occurrenceRouteDescriptors source).flatMap fun descriptor =>
        if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundaryBlock else [] := by
  unfold splitRouteDescriptors
  rw [List.flatMap_append]
  have prefixEq :
      (occurrenceRouteDescriptors source).flatMap
          routedVariableNumericBoundaryDescriptorBlock =
        (occurrenceRouteDescriptors source).flatMap fun descriptor =>
          if descriptor.offset = ((1, 0) : Cell) then
            routedVariableNextBoundaryBlock else [] := by
    apply List.flatMap_congr
    intro descriptor descriptorMember
    unfold routedVariableNumericBoundaryDescriptorBlock
    have rankZero := occurrenceRouteDescriptor_targetPortRank_eq_zero
      source descriptorMember
    simp [rankZero]
  have suffixEq :
      (cycleLinkRouteDescriptors source).flatMap
          routedVariableNumericBoundaryDescriptorBlock = [] := by
    calc
      _ = (cycleLinkRouteDescriptors source).flatMap (fun _ => []) := by
          apply List.flatMap_congr
          intro descriptor descriptorMember
          unfold routedVariableNumericBoundaryDescriptorBlock
          have positive := cycleLinkRouteDescriptor_targetPortRank_ne_zero
            source descriptorMember
          simp [positive]
      _ = [] := by simp
  rw [prefixEq, suffixEq, List.append_nil]

end LeanTrominoes.PeriodicThreeSATThree
