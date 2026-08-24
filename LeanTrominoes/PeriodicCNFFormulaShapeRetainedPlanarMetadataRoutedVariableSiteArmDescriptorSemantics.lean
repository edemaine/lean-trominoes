/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmDescriptorData

/-! # Descriptor expansion of routed-variable site-arm scans -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Site-arm descriptor expansion distributes over concatenation. -/
theorem routedVariableSiteArmDescriptorStream_append
    (first second : List (List PlanarThreeSAT.DuplicatorArm)) :
    routedVariableSiteArmDescriptorStream (first ++ second) =
      routedVariableSiteArmDescriptorStream first ++
        routedVariableSiteArmDescriptorStream second := by
  unfold routedVariableSiteArmDescriptorStream
  rw [List.flatMap_append]

/-- Repeating one arm list repeats its expanded descriptor block. -/
theorem routedVariableSiteArmDescriptorStream_replicate
    (count : Nat) (arms : List PlanarThreeSAT.DuplicatorArm) :
    routedVariableSiteArmDescriptorStream
        (List.replicate count arms) =
      (List.replicate count
        (arms.flatMap routedVariableCurrentArmBlock)).flatten := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.flatten_cons,
        routedVariableSiteArmDescriptorStream,
        List.flatMap_cons]
      exact congrArg
        (List.append (arms.flatMap routedVariableCurrentArmBlock))
        induction

/-- Expanding the three ordered arms of a full site gives its established
descriptor block. -/
theorem routedVariableFullSiteArms_descriptorBlock :
    routedVariableFullSiteArms.flatMap
        routedVariableCurrentArmBlock =
      routedVariableFullSiteBlock := by
  rfl

/-- Expanding the two ordered cycle-only arms gives its established block. -/
theorem routedVariableCycleOnlySiteArms_descriptorBlock :
    routedVariableCycleOnlySiteArms.flatMap
        routedVariableCurrentArmBlock =
      routedVariableCycleOnlySiteBlock := by
  rfl

/-- The three boundary singleton arms expand to the established boundary
descriptor block. -/
theorem routedVariableNextBoundarySiteArmDescriptorStream :
    routedVariableSiteArmDescriptorStream
        routedVariableNextBoundarySiteArmBlocks =
      routedVariableNextBoundaryBlock := by
  rfl

/-- Nine full sites expand to the established current-cycle block. -/
theorem routedVariableCurrentCycleSiteArmDescriptorStream :
    routedVariableSiteArmDescriptorStream
        routedVariableCurrentCycleSiteArmBlocks =
      routedVariableCurrentCycleBlock := by
  unfold routedVariableCurrentCycleSiteArmBlocks
    routedVariableCurrentCycleBlock
  rw [routedVariableSiteArmDescriptorStream_replicate,
    routedVariableFullSiteArms_descriptorBlock]

/-- Three cycle-only and six full sites expand to the established next-cycle
block. -/
theorem routedVariableNextCycleSiteArmDescriptorStream :
    routedVariableSiteArmDescriptorStream
        routedVariableNextCycleSiteArmBlocks =
      routedVariableNextCycleBlock := by
  unfold routedVariableNextCycleSiteArmBlocks
    routedVariableNextCycleBlock
  rw [routedVariableSiteArmDescriptorStream_append,
    routedVariableSiteArmDescriptorStream_replicate,
    routedVariableSiteArmDescriptorStream_replicate,
    routedVariableCycleOnlySiteArms_descriptorBlock,
    routedVariableFullSiteArms_descriptorBlock]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
