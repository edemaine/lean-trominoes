/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCycleRows
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableOccurrenceRows

/-! # Exact routed-variable pair scan of split descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The complete split descriptor square emits the occurrence-boundary
prefix followed by one indexed cycle block per rotated target vertex. -/
theorem routedVariablePairDescriptorScan_splitRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariablePairDescriptorScan (splitRouteDescriptors source) =
      ((occurrenceRouteDescriptors source).flatMap fun descriptor =>
        if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundaryBlock else []) ++
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (routedVariableCycleBlockAtTargetIndex source) := by
  unfold routedVariablePairDescriptorScan
  change
    ((splitRouteDescriptors source).flatMap fun first =>
      (splitRouteDescriptors source).map fun second =>
        (first, second)).flatMap routedVariablePairDescriptorBlock = _
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  let row := fun first : PeriodicOrthocrossing.RouteDescriptor =>
    (splitRouteDescriptors source).flatMap fun second =>
      routedVariablePairDescriptorBlock (first, second)
  calc
    (splitRouteDescriptors source).flatMap row =
      (occurrenceRouteDescriptors source ++
        cycleLinkRouteDescriptors source).flatMap row := by rfl
    _ = (occurrenceRouteDescriptors source).flatMap row ++
        (cycleLinkRouteDescriptors source).flatMap row := by
          rw [List.flatMap_append]
    _ = ((occurrenceRouteDescriptors source).flatMap fun descriptor =>
          if descriptor.offset = ((1, 0) : Cell) then
            routedVariableNextBoundaryBlock else []) ++
        (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
            (routedVariableCycleBlockAtTargetIndex source) := by
          rw [splitRouteDescriptor_occurrenceRows,
            splitRouteDescriptor_cycleRows]

end PeriodicThreeSATThree
end LeanTrominoes
