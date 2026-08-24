/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericSiteArmScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData

/-! # Descriptor-block counterpart of the numeric routed-variable arm scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Descriptor block contributed by one possible positive-offset boundary
incidence. -/
def routedVariableNumericBoundaryDescriptorBlock
    (descriptor : RouteDescriptor) :
    List FormulaShapeDirectionOrdering.Token :=
  if descriptor.targetPortRank = 0 ∧
      descriptor.offset = ((1, 0) : Cell) then
    routedVariableNextBoundaryBlock
  else
    []

/-- Descriptor block selected at one numeric target vertex. -/
def routedVariableNumericCycleDescriptorBlockAtTargetIndex
    (descriptors : List RouteDescriptor) (targetIndex : Nat) :
    List FormulaShapeDirectionOrdering.Token :=
  match occurrenceDescriptorAtTargetIndex descriptors targetIndex with
  | some descriptor =>
      (if descriptor.offset = ((0, 0) : Cell) then
          routedVariableCurrentCycleBlock else []) ++
        (if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextCycleBlock else [])
  | none => []

/-- Boundary-prefix/cycle-suffix descriptor scan selected from numeric route
descriptors. -/
def routedVariableNumericDescriptorScan
    (descriptors : List RouteDescriptor) (targetCount : Nat) :
    List FormulaShapeDirectionOrdering.Token :=
  descriptors.flatMap routedVariableNumericBoundaryDescriptorBlock ++
    (List.range targetCount).flatMap
      (routedVariableNumericCycleDescriptorBlockAtTargetIndex descriptors)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
