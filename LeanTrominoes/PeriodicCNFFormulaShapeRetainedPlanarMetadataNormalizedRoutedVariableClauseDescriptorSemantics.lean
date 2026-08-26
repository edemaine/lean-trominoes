/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCurrentSliceFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizationArmClassification

/-! # Descriptors indexed by normalized routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The finite descriptor selected by one normalized routed-variable link
and implication direction. -/
def normalizedRoutedVariableClauseDescriptor
    {Variable : Type}
    (taggedLink : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) × Bool) :
    FormulaShapeDirectionOrdering.Token :=
  routedVariableClauseDescriptor
    (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
    false taggedLink.2

/-- Descriptor stream over the raw normalized routed-variable link and
direction presentation. -/
def normalizedRoutedVariableClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (((drawingRoutedVariableLinks source).map
      (PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization source))).product
    [true, false]).map normalizedRoutedVariableClauseDescriptor

/-- The normalized-pair descriptor stream expands each source link into its
canonical two-clause block. -/
theorem normalizedRoutedVariableClauseDescriptors_eq_flatMap_blocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    normalizedRoutedVariableClauseDescriptors source =
      (drawingRoutedVariableLinks source).flatMap fun link =>
        canonicalRoutedVariableDescriptorBlock
          (wrappedNormalizedRoutedVariableLinkArm
            (PeriodicEquality.normalizeLink
              (externalWrappedVariableNormalization source) link))
          false := by
  unfold normalizedRoutedVariableClauseDescriptors
  induction drawingRoutedVariableLinks source with
  | nil => rfl
  | cons link links induction =>
      change
        normalizedRoutedVariableClauseDescriptor
              (PeriodicEquality.normalizeLink
                (externalWrappedVariableNormalization source) link, true) ::
            normalizedRoutedVariableClauseDescriptor
              (PeriodicEquality.normalizeLink
                (externalWrappedVariableNormalization source) link, false) ::
            List.map normalizedRoutedVariableClauseDescriptor
              ((List.map
                (PeriodicEquality.normalizeLink
                  (externalWrappedVariableNormalization source))
                links).product [true, false]) =
          canonicalRoutedVariableDescriptorBlock
              (wrappedNormalizedRoutedVariableLinkArm
                (PeriodicEquality.normalizeLink
                  (externalWrappedVariableNormalization source) link))
              false ++
            List.flatMap
              (fun link =>
                canonicalRoutedVariableDescriptorBlock
                  (wrappedNormalizedRoutedVariableLinkArm
                    (PeriodicEquality.normalizeLink
                      (externalWrappedVariableNormalization source) link))
                  false)
              links
      rw [induction]
      rfl

/-- For a well-formed local source, descriptors indexed by normalized links
are exactly the retained routed-variable metadata descriptor family. -/
theorem routedVariableMetadataClauseDescriptors_eq_normalizedPairs
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (isLocal : source.incidenceGraph.IsLocal) :
    routedVariableMetadataClauseDescriptors source =
      normalizedRoutedVariableClauseDescriptors source := by
  rw [routedVariableMetadataClauseDescriptors_eq_currentSliceCanonicalBlocks
    source wellFormed isLocal]
  calc
    (drawingVariableRouteSites source).flatMap (fun site =>
        (routedVariableLinksAt source site).zipIdx.flatMap
          (fun taggedLink =>
            canonicalRoutedVariableDescriptorBlock
              taggedLink.1.first.duplicatorArm false)) =
      (drawingVariableRouteSites source).flatMap (fun site =>
        (routedVariableLinksAt source site).flatMap
          (fun link =>
            canonicalRoutedVariableDescriptorBlock
              link.first.duplicatorArm false)) := by
        apply List.flatMap_congr
        intro site _siteMember
        exact PeriodicCNF.zipIdx_flatMap_fst
          (fun link =>
            canonicalRoutedVariableDescriptorBlock
              link.first.duplicatorArm false)
          (routedVariableLinksAt source site) 0
    _ = (drawingRoutedVariableLinks source).flatMap
        (fun link =>
          canonicalRoutedVariableDescriptorBlock
            link.first.duplicatorArm false) := by
        unfold drawingRoutedVariableLinks
        rw [List.flatMap_assoc]
    _ = (drawingRoutedVariableLinks source).flatMap
        (fun link =>
          canonicalRoutedVariableDescriptorBlock
            (wrappedNormalizedRoutedVariableLinkArm
              (PeriodicEquality.normalizeLink
                (externalWrappedVariableNormalization source) link))
            false) := by
        apply List.flatMap_congr
        intro link linkMember
        rw [wrappedNormalizedRoutedVariableLinkArm_normalizeLink
          source link linkMember]
    _ = normalizedRoutedVariableClauseDescriptors source :=
      (normalizedRoutedVariableClauseDescriptors_eq_flatMap_blocks
        source).symm

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
