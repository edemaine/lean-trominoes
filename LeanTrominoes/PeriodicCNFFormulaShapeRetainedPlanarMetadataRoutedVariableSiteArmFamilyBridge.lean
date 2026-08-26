/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCurrentSliceFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSemanticDescriptorScan
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmFamilySemantics

/-! # Site-arm presentation of the routed-variable descriptor family -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- On local well-formed inputs, the retained routed-variable family is the
descriptor expansion of the numeric active-arm scan in semantic site order. -/
theorem
    routedVariableMetadataClauseDescriptors_eq_numericOccurrenceSiteArmStream
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (isLocal : source.incidenceGraph.IsLocal) :
    routedVariableMetadataClauseDescriptors source =
      routedVariableSiteArmDescriptorStream
        (routedVariableNumericOccurrenceSiteArmScan source) := by
  rw [routedVariableMetadataClauseDescriptors_eq_currentSliceCanonicalBlocks
    source wellFormed isLocal]
  calc
    (drawingVariableRouteSites source).flatMap (fun site =>
        (routedVariableLinksAt source site).zipIdx.flatMap fun taggedLink =>
          canonicalRoutedVariableDescriptorBlock
            taggedLink.1.first.duplicatorArm false) =
        routedVariableSiteArmDescriptorStream
          (routedVariableSemanticSiteArmScan source) := by
      unfold routedVariableSemanticSiteArmScan
      exact routedVariableCanonicalBlocks_eq_siteArmDescriptorStream
        (drawingVariableRouteSites source)
        (routedVariableLinksAt source)
        (fun link => link.first.duplicatorArm)
    _ = _ :=
      routedVariableSemanticSiteArmDescriptorStream_eq_numericOccurrence
        source

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
