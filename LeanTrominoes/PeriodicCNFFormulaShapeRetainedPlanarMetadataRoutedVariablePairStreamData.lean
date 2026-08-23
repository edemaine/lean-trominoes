/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairCompiledData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Compiled routed-variable descriptor stream over ordered pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Independently evaluate every complete tagged descriptor-pair block. -/
def compiledRoutedVariablePairDescriptorStream
    (tokens : List Token) :
    List FormulaShapeDirectionOrdering.Token :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    compiledRoutedVariablePairDescriptorBlock tokens

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
