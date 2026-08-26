/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData

/-! # Normalized routed-variable descriptor-pair scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- After periodic normalization, either cycle case contributes one copy of
the three distinct arm links.  The boundary-only copies and the remaining
translated repetitions are duplicate normalized links. -/
def normalizedRoutedVariablePairDescriptorBlock
    (pair : RouteDescriptor × RouteDescriptor) :
    List FormulaShapeDirectionOrdering.Token :=
  (if routedVariableCurrentCyclePair pair then
      routedVariableFullSiteBlock else []) ++
    (if routedVariableNextCyclePair pair then
      routedVariableFullSiteBlock else [])

/-- Row-major scan retaining one descriptor block per normalized routed
variable triple. -/
def normalizedRoutedVariablePairDescriptorScan
    (descriptors : List RouteDescriptor) :
    List FormulaShapeDirectionOrdering.Token :=
  (descriptors ×ˢ descriptors).flatMap
    normalizedRoutedVariablePairDescriptorBlock

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
