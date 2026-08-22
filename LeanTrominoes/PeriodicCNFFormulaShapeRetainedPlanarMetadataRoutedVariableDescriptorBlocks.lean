/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendFamilySemantics

/-! # Per-link routed-variable clause-descriptor blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The two local clause descriptors contributed by one active
routed-variable equality arm. -/
def routedVariableLinkClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATRoutedVariableClauseMetadataFor
      site armIndex arm link).map
    (metadataClauseDescriptor source)

@[simp] theorem routedVariableLinkClauseDescriptors_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (routedVariableLinkClauseDescriptors
      source site armIndex arm link).length = 2 := by
  simp [routedVariableLinkClauseDescriptors,
    drawingPlanarSATRoutedVariableClauseMetadataFor,
    drawingPlanarSATRoutedVariableFormulaAt, equalityInstance]

/-- The complete routed-variable descriptor family is the nested
presentation-order concatenation of its two-token active-arm blocks. -/
theorem routedVariableMetadataClauseDescriptors_eq_flatMap_linkBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedVariableMetadataClauseDescriptors source =
      (drawingVariableRouteSites source).flatMap fun site =>
        (routedVariableLinksAt source site).zipIdx.flatMap fun taggedLink =>
          routedVariableLinkClauseDescriptors source site taggedLink.2
            taggedLink.1.first.duplicatorArm taggedLink.1 := by
  unfold routedVariableMetadataClauseDescriptors
    drawingPlanarSATRoutedVariableClauseMetadata
  simp only [List.map_flatMap]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
