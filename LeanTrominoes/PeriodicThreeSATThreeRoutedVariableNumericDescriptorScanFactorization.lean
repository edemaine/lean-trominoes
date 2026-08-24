/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeSplitNumericBoundaryDescriptorScan
import LeanTrominoes.PeriodicThreeSATThreeSplitNumericCycleDescriptorScan

/-! # Boundary/cycle factorization of the split numeric descriptor scan -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The split numeric descriptor scan factors into its copied-occurrence
boundary prefix and target-indexed cycle suffix. -/
theorem routedVariableNumericDescriptorScan_splitRouteDescriptors_eq_blocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariableNumericDescriptorScan
        (splitRouteDescriptors source)
        (PeriodicCNF.presentationLiteralCount source) =
      ((occurrenceRouteDescriptors source).flatMap fun descriptor =>
        if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundaryBlock else []) ++
      (List.range
        (PeriodicCNF.presentationLiteralCount source)).flatMap
          (routedVariableCycleBlockAtTargetIndex source) := by
  unfold routedVariableNumericDescriptorScan
  rw [splitRouteDescriptors_numericBoundaryDescriptorBlocks]
  congr 1
  apply List.flatMap_congr
  intro targetIndex _targetIndexMember
  exact
    splitRouteDescriptors_numericCycleDescriptorBlockAtTargetIndex
      source targetIndex

end LeanTrominoes.PeriodicThreeSATThree
