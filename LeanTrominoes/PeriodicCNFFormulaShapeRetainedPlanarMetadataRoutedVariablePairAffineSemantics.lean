/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableBoundaryAffineSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCurrentCycleAffineSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNextCycleAffineSemantics

/-! # Combined affine semantics of routed-variable descriptor pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

@[simp] theorem routedVariablePairAffinePredicates_map_evalPair
    (pair : RouteDescriptor × RouteDescriptor) :
    routedVariablePairAffinePredicates.map
        (fun predicate => predicate.evalPair pair) =
      [routedVariableNextBoundaryPair pair,
        routedVariableCurrentCyclePair pair,
        routedVariableNextCyclePair pair] := by
  simp [routedVariablePairAffinePredicates]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
