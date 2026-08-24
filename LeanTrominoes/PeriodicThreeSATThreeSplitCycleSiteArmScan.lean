/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeSplitCycleSiteArmBlockAtAtom

/-! # Split numeric cycle arm scan in rotated occurrence order -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Concatenating semantic atom-indexed cycle blocks equals the numeric split
cycle scan over the canonical target-index range. -/
theorem rotatedOccurrenceVariables_cycleSiteArmBlocks_eq_numeric
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (rotatedOccurrenceVariables source).flatMap
        (routedVariableCycleSiteArmBlocksAtAtom source) =
      (List.range
        (PeriodicCNF.presentationLiteralCount source)).flatMap
          (routedVariableCycleSiteArmBlocksAtTargetIndex
            (splitRouteDescriptors source)) := by
  calc
    _ = (rotatedOccurrenceVariables source).flatMap fun atom =>
          routedVariableCycleSiteArmBlocksAtTargetIndex
            (splitRouteDescriptors source)
            ((rotatedOccurrenceVariables source).idxOf atom) := by
      apply List.flatMap_congr
      intro atom atomMember
      exact (splitRouteDescriptors_cycleSiteArmBlockAtAtom_eq
        source atom atomMember).symm
    _ = ((rotatedOccurrenceVariables source).map fun atom =>
          (rotatedOccurrenceVariables source).idxOf atom).flatMap
            (routedVariableCycleSiteArmBlocksAtTargetIndex
              (splitRouteDescriptors source)) := by
      rw [List.flatMap_map]
    _ = (List.range (rotatedOccurrenceVariables source).length).flatMap
          (routedVariableCycleSiteArmBlocksAtTargetIndex
            (splitRouteDescriptors source)) := by
      rw [List.map_idxOf_self_eq_range_beq _
        (rotatedOccurrenceVariables_nodup source)]
    _ = _ := by rw [rotatedOccurrenceVariables_length]

end LeanTrominoes.PeriodicThreeSATThree
