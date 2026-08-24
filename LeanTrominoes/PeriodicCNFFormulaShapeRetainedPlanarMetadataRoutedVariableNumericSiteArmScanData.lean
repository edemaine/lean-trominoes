/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Numeric routed-variable site-arm scans -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Find the first rank-zero occurrence descriptor at a target vertex in an
arbitrary numeric descriptor stream. -/
def occurrenceDescriptorAtTargetIndex
    (descriptors : List RouteDescriptor) (targetIndex : Nat) :
    Option RouteDescriptor :=
  descriptors.find? fun descriptor =>
    decide (descriptor.targetPortRank = 0 ∧
      descriptor.targetVertexIndex = targetIndex)

/-- Boundary-only site arms contributed by one rank-zero occurrence
descriptor. -/
def routedVariableBoundarySiteArmBlocks
    (descriptor : RouteDescriptor) : List (List DuplicatorArm) :=
  if descriptor.targetPortRank = 0 ∧
      descriptor.offset = ((1, 0) : Cell) then
    routedVariableNextBoundarySiteArmBlocks
  else
    []

/-- Cycle-site arms selected at one numeric target vertex. -/
def routedVariableCycleSiteArmBlocksAtTargetIndex
    (descriptors : List RouteDescriptor) (targetIndex : Nat) :
    List (List DuplicatorArm) :=
  match occurrenceDescriptorAtTargetIndex descriptors targetIndex with
  | some descriptor =>
      (if descriptor.offset = ((0, 0) : Cell) then
          routedVariableCurrentCycleSiteArmBlocks else []) ++
        (if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextCycleSiteArmBlocks else [])
  | none => []

/-- Site-major active-arm stream obtained from numeric occurrence
descriptors and a target-vertex range. -/
def routedVariableNumericSiteArmScan
    (descriptors : List RouteDescriptor) (targetCount : Nat) :
    List (List DuplicatorArm) :=
  descriptors.flatMap routedVariableBoundarySiteArmBlocks ++
    (List.range targetCount).flatMap
      (routedVariableCycleSiteArmBlocksAtTargetIndex descriptors)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
