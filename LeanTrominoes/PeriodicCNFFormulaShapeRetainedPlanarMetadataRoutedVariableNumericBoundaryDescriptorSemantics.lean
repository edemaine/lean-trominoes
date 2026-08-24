/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericDescriptorScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmDescriptorSemantics

/-! # Descriptor expansion of numeric routed-variable boundary arms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Expanding the boundary arms selected by one numeric descriptor gives its
boundary descriptor block. -/
theorem routedVariableBoundarySiteArmBlocks_descriptorStream
    (descriptor : RouteDescriptor) :
    routedVariableSiteArmDescriptorStream
        (routedVariableBoundarySiteArmBlocks descriptor) =
      routedVariableNumericBoundaryDescriptorBlock descriptor := by
  unfold routedVariableBoundarySiteArmBlocks
    routedVariableNumericBoundaryDescriptorBlock
  by_cases selected : descriptor.targetPortRank = 0 ∧
      descriptor.offset = ((1, 0) : Cell)
  · simp only [if_pos selected]
    exact routedVariableNextBoundarySiteArmDescriptorStream
  · simp only [if_neg selected,
      routedVariableSiteArmDescriptorStream]
    rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
