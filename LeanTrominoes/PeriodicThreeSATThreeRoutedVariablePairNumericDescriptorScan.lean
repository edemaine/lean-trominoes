/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableNumericDescriptorScanFactorization
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariablePairScan

/-! # Equality of split routed-variable descriptor scans -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The row-major finite descriptor-pair scan and the site-major numeric scan
emit exactly the same routed-variable clause descriptors for the split
formula. -/
theorem routedVariablePairDescriptorScan_splitRouteDescriptors_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariablePairDescriptorScan (splitRouteDescriptors source) =
      routedVariableNumericDescriptorScan
        (splitRouteDescriptors source)
        (PeriodicCNF.presentationLiteralCount source) :=
  (routedVariablePairDescriptorScan_splitRouteDescriptors source).trans
    (routedVariableNumericDescriptorScan_splitRouteDescriptors_eq_blocks
      source).symm

end LeanTrominoes.PeriodicThreeSATThree
