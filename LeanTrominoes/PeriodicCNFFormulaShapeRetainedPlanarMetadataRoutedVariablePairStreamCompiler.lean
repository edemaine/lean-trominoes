/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairCompiledCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairStreamData
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Polynomial-time routed-variable descriptor-pair stream compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Computability Turing
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Map the verified local evaluator independently over every canonical
descriptor-pair block in polynomial time. -/
noncomputable def
    compiledRoutedVariablePairDescriptorStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      compiledRoutedVariablePairDescriptorStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    compiledRoutedVariablePairDescriptorBlockComputableInPolyTime
    isPairEnd

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

end
