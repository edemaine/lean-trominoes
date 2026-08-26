/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairCompiledData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for normalized routed-variable pair blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Computability Turing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- The three affine guards followed by the finite normalized decoder are
polynomial time. -/
noncomputable def
    compiledNormalizedRoutedVariablePairDescriptorBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      compiledNormalizedRoutedVariablePairDescriptorBlock := by
  let predicates := predicateListTruthValuesComputableInPolyTime
    routedVariablePairAffinePredicates
  let decode := FixedLengthWordEvaluator.computableInPolyTime 3
    normalizedRoutedVariablePairTruthDescriptorBlock
  let complete :=
    TM2CompositionMachine.computableInPolyTime predicates decode
  change TM2ComputableInPolyTime id id
    (fun tokens => FixedLengthWordEvaluator.output 3
      normalizedRoutedVariablePairTruthDescriptorBlock
      (predicateListTruthValues routedVariablePairAffinePredicates tokens))
  exact complete

/-- Map the normalized local evaluator over the complete tagged pair stream. -/
noncomputable def
    compiledNormalizedRoutedVariablePairDescriptorStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      compiledNormalizedRoutedVariablePairDescriptorStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    compiledNormalizedRoutedVariablePairDescriptorBlockComputableInPolyTime
    isPairEnd

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

end
