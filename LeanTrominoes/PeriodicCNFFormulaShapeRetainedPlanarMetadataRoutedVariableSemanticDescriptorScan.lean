/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSemanticSiteArmScan
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmDescriptorData

/-! # Descriptor expansion of semantic routed-variable arms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Expanding semantic active-link arms or their numeric occurrence-rank
interpretation produces the same descriptor stream. -/
theorem routedVariableSemanticSiteArmDescriptorStream_eq_numericOccurrence
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariableSiteArmDescriptorStream
        (routedVariableSemanticSiteArmScan source) =
      routedVariableSiteArmDescriptorStream
        (routedVariableNumericOccurrenceSiteArmScan source) :=
  congrArg routedVariableSiteArmDescriptorStream
    (routedVariableSemanticSiteArmScan_eq_numericOccurrence source)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
