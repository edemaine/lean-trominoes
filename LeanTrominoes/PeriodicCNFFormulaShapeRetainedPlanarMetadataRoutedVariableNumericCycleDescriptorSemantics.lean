/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericDescriptorScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmDescriptorSemantics

/-! # Descriptor expansion of numeric routed-variable cycle arms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Expanding the arm blocks selected at one numeric target vertex gives its
cycle descriptor block. -/
theorem routedVariableCycleSiteArmBlocksAtTargetIndex_descriptorStream
    (descriptors : List RouteDescriptor) (targetIndex : Nat) :
    routedVariableSiteArmDescriptorStream
        (routedVariableCycleSiteArmBlocksAtTargetIndex
          descriptors targetIndex) =
      routedVariableNumericCycleDescriptorBlockAtTargetIndex
        descriptors targetIndex := by
  unfold routedVariableCycleSiteArmBlocksAtTargetIndex
    routedVariableNumericCycleDescriptorBlockAtTargetIndex
  cases lookup : occurrenceDescriptorAtTargetIndex
      descriptors targetIndex with
  | none =>
      simp only [routedVariableSiteArmDescriptorStream,
        List.flatMap_nil]
  | some descriptor =>
      rw [routedVariableSiteArmDescriptorStream_append]
      congr 1
      · by_cases current : descriptor.offset = ((0, 0) : Cell)
        · rw [if_pos current, if_pos current]
          exact routedVariableCurrentCycleSiteArmDescriptorStream
        · rw [if_neg current, if_neg current]
          simp only [routedVariableSiteArmDescriptorStream,
            List.flatMap_nil]
      · by_cases next : descriptor.offset = ((1, 0) : Cell)
        · rw [if_pos next, if_pos next]
          exact routedVariableNextCycleSiteArmDescriptorStream
        · rw [if_neg next, if_neg next]
          simp only [routedVariableSiteArmDescriptorStream,
            List.flatMap_nil]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
