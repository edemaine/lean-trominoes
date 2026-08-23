/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairCompiledData
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time compiler for one routed-variable descriptor pair -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Computability Turing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- Evaluate the three fixed affine guards and decode their finite truth word
in polynomial time. -/
noncomputable def
    compiledRoutedVariablePairDescriptorBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      compiledRoutedVariablePairDescriptorBlock := by
  let predicates := predicateListTruthValuesComputableInPolyTime
    routedVariablePairAffinePredicates
  let decode := FixedLengthWordEvaluator.computableInPolyTime 3
    routedVariablePairTruthDescriptorBlock
  let complete := TM2CompositionMachine.computableInPolyTime
    predicates decode
  exact complete

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

end
