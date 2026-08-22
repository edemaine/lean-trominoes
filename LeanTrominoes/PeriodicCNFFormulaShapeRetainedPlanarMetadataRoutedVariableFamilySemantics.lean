/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorSemanticsAt

/-! # Complete routed-variable descriptor-family semantics -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- One active routed-variable arm contributes exactly its canonical finite
two-token descriptor block. -/
theorem routedVariableLinkClauseDescriptors_eq_canonicalBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    routedVariableLinkClauseDescriptors
        source site armIndex arm link =
      canonicalRoutedVariableDescriptorBlock arm
        (routedVariableLinkNextSlice source link) := by
  rw [routedVariableLinkClauseDescriptors_eq_pair]
  unfold canonicalRoutedVariableDescriptorBlock
  rw [metadataClauseDescriptor_routedVariableClauseMetadataAt_eq
      source site armIndex arm link true,
    metadataClauseDescriptor_routedVariableClauseMetadataAt_eq
      source site armIndex arm link false]

/-- The complete routed-variable family is a finite two-token expansion of
the active links in its exact site and arm presentation order. -/
theorem routedVariableMetadataClauseDescriptors_eq_canonicalBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariableMetadataClauseDescriptors source =
      (drawingVariableRouteSites source).flatMap fun site =>
        (routedVariableLinksAt source site).zipIdx.flatMap fun taggedLink =>
          canonicalRoutedVariableDescriptorBlock
            taggedLink.1.first.duplicatorArm
            (routedVariableLinkNextSlice source taggedLink.1) := by
  rw [routedVariableMetadataClauseDescriptors_eq_flatMap_linkBlocks]
  apply List.flatMap_congr
  intro site _
  apply List.flatMap_congr
  intro taggedLink _
  exact routedVariableLinkClauseDescriptors_eq_canonicalBlock
    source site taggedLink.2 taggedLink.1.first.duplicatorArm taggedLink.1

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
