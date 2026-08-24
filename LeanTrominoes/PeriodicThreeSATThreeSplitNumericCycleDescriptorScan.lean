/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericDescriptorScanData
import LeanTrominoes.PeriodicThreeSATThreeSplitOccurrenceDescriptorLookup

/-! # Cycle descriptor blocks of the split route stream -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- At every target index, the numeric split-stream cycle block is the
established copied-occurrence cycle block. -/
theorem splitRouteDescriptors_numericCycleDescriptorBlockAtTargetIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (targetIndex : Nat) :
    routedVariableNumericCycleDescriptorBlockAtTargetIndex
        (splitRouteDescriptors source) targetIndex =
      routedVariableCycleBlockAtTargetIndex source targetIndex := by
  unfold routedVariableNumericCycleDescriptorBlockAtTargetIndex
    routedVariableCycleBlockAtTargetIndex
  rw [occurrenceDescriptorAtTargetIndex_splitRouteDescriptors]
  cases occurrenceRouteDescriptorAtTargetIndex source targetIndex <;> rfl

end LeanTrominoes.PeriodicThreeSATThree
