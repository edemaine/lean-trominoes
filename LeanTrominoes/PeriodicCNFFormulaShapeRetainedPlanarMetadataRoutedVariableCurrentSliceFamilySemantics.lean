/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNextSliceSemantics

/-! # Current-slice routed-variable descriptor-family semantics -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every retained routed-variable link contributes its canonical current-slice
two-token block. -/
theorem routedVariableMetadataClauseDescriptors_eq_currentSliceCanonicalBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (isLocal : source.incidenceGraph.IsLocal) :
    routedVariableMetadataClauseDescriptors source =
      (drawingVariableRouteSites source).flatMap fun site =>
        (routedVariableLinksAt source site).zipIdx.flatMap fun taggedLink =>
          canonicalRoutedVariableDescriptorBlock
            taggedLink.1.first.duplicatorArm false := by
  rw [routedVariableMetadataClauseDescriptors_eq_canonicalBlocks]
  apply List.flatMap_congr
  intro site _siteMember
  apply List.flatMap_congr
  intro taggedLink taggedLinkMember
  rw [routedVariableLinkNextSlice_eq_false source wellFormed isLocal site
    taggedLink.1 (List.fst_mem_of_mem_zipIdx taggedLinkMember)]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
