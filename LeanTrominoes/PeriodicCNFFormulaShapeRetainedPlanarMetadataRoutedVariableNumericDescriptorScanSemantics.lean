/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericBoundaryDescriptorSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericCycleDescriptorSemantics

/-! # Descriptor expansion of the numeric routed-variable site-arm scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Expanding a concatenation of site-arm blocks can be performed one source
value at a time. -/
theorem routedVariableSiteArmDescriptorStream_flatMap
    {Value : Type*} (values : List Value)
    (blocks : Value → List (List PlanarThreeSAT.DuplicatorArm)) :
    routedVariableSiteArmDescriptorStream (values.flatMap blocks) =
      values.flatMap fun value =>
        routedVariableSiteArmDescriptorStream (blocks value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.flatMap_cons,
        routedVariableSiteArmDescriptorStream_append,
        List.flatMap_cons, induction]

/-- The numeric site-arm scan expands exactly to its descriptor-block
counterpart. -/
theorem routedVariableNumericSiteArmScan_descriptorStream
    (descriptors : List RouteDescriptor) (targetCount : Nat) :
    routedVariableSiteArmDescriptorStream
        (routedVariableNumericSiteArmScan descriptors targetCount) =
      routedVariableNumericDescriptorScan descriptors targetCount := by
  unfold routedVariableNumericSiteArmScan
    routedVariableNumericDescriptorScan
  rw [routedVariableSiteArmDescriptorStream_append,
    routedVariableSiteArmDescriptorStream_flatMap,
    routedVariableSiteArmDescriptorStream_flatMap]
  congr 1
  · apply List.flatMap_congr
    intro descriptor _descriptorMember
    exact routedVariableBoundarySiteArmBlocks_descriptorStream descriptor
  · apply List.flatMap_congr
    intro targetIndex _targetIndexMember
    exact
      routedVariableCycleSiteArmBlocksAtTargetIndex_descriptorStream
        descriptors targetIndex

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
