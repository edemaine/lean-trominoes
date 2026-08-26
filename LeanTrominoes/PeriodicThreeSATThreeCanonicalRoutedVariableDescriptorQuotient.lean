/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmDescriptorSemantics
import LeanTrominoes.PeriodicThreeSATThreeCanonicalRoutedVariableArmOrder
import LeanTrominoes.PeriodicThreeSATThreeCanonicalRoutedVariableRepresentativeDescriptors
import LeanTrominoes.PeriodicThreeSATThreeRotatedOccurrenceVariablesBasic

/-! # Public descriptor quotient of canonical routed-variable clauses -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Expanding both implication directions of normalized links is the flat
map of their classified two-token arm blocks. -/
theorem normalizedRoutedVariableTaggedLinkDescriptors_eq_armBlocks
    {Variable : Type}
    (links : List (PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable))) :
    ((links.product [true, false]).map
        normalizedRoutedVariableClauseDescriptor) =
      links.flatMap fun link =>
        routedVariableCurrentArmBlock
          (wrappedNormalizedRoutedVariableLinkArm link) := by
  induction links with
  | nil => rfl
  | cons link links induction =>
      change
        normalizedRoutedVariableClauseDescriptor (link, true) ::
            normalizedRoutedVariableClauseDescriptor (link, false) ::
            ((links.product [true, false]).map
              normalizedRoutedVariableClauseDescriptor) =
          routedVariableCurrentArmBlock
              (wrappedNormalizedRoutedVariableLinkArm link) ++
            links.flatMap (fun link =>
              routedVariableCurrentArmBlock
                (wrappedNormalizedRoutedVariableLinkArm link))
      rw [induction]
      rfl

/-- The canonical normalized routed-variable descriptor stream is one
complete six-token site block for every source literal occurrence. -/
theorem canonicalNormalizedRoutedVariableDescriptors_eq_fullSites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    ((canonicalWrappedNormalizedRoutedVariableLinks source).product
        [true, false]).map normalizedRoutedVariableClauseDescriptor =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  rw [normalizedRoutedVariableTaggedLinkDescriptors_eq_armBlocks]
  calc
    (canonicalWrappedNormalizedRoutedVariableLinks source).flatMap
        (fun link => routedVariableCurrentArmBlock
          (wrappedNormalizedRoutedVariableLinkArm link)) =
      ((canonicalWrappedNormalizedRoutedVariableLinks source).map
        wrappedNormalizedRoutedVariableLinkArm).flatMap
          routedVariableCurrentArmBlock := by
            rw [List.flatMap_map]
    _ = ((rotatedOccurrenceVariables source).flatMap
          (fun _atom => routedVariableFullSiteArms)).flatMap
            routedVariableCurrentArmBlock := by
      rw [canonicalWrappedNormalizedRoutedVariableLinkArms_eq_fullSites
        source positiveOffsets]
    _ = (rotatedOccurrenceVariables source).flatMap
          (fun _atom =>
            routedVariableFullSiteArms.flatMap
              routedVariableCurrentArmBlock) := by
      rw [List.flatMap_assoc]
    _ = (rotatedOccurrenceVariables source).flatMap
          (fun _atom => routedVariableFullSiteBlock) := by
      apply List.flatMap_congr
      intro atom _atomMember
      exact routedVariableFullSiteArms_descriptorBlock
    _ = (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
          (fun _targetIndex => routedVariableFullSiteBlock) := by
      have flatMapConstant : ∀ {Index : Type} (items : List Index),
          items.flatMap (fun _item => routedVariableFullSiteBlock) =
            (List.replicate items.length
              routedVariableFullSiteBlock).flatten := by
        intro Index items
        induction items with
        | nil => rfl
        | cons item items induction =>
            simp only [List.flatMap_cons, List.length_cons,
              List.replicate_succ, List.flatten_cons]
            rw [induction]
      rw [flatMapConstant, flatMapConstant, List.length_range,
        rotatedOccurrenceVariables_length]

/-- Public representative descriptors of the canonical deduplicated
routed-variable clauses are exactly the finite full-site quotient. -/
theorem canonicalRoutedVariableRepresentativeDescriptors_eq_fullSites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (canonicalWrappedNormalizedRoutedVariableClauses source).map
        (representativeClauseDescriptor (formula source)) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  rw [canonicalWrappedNormalizedRoutedVariableClauses_map_representative
    source sourceLocal sourceWidth positiveOffsets]
  exact canonicalNormalizedRoutedVariableDescriptors_eq_fullSites
    source positiveOffsets

end LeanTrominoes.PeriodicThreeSATThree
