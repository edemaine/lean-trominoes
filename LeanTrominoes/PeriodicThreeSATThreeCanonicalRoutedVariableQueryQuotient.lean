/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCanonicalRoutedVariableDescriptorQuotient
import LeanTrominoes.RetainedAngularFanFinalRoutedVariableQueryPostprocess

/-! # Stable-query quotient of canonical routed-variable clauses -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

/-- The stable direct queries indexed by canonical normalized links are one
complete six-query block for every source literal occurrence. -/
theorem canonicalRoutedVariableQueries_eq_fullSites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    ((canonicalWrappedNormalizedRoutedVariableLinks source).product
        [true, false]).map (fun taggedLink =>
          retainedFinalDirectRoutedVariableClauseQuery
            (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
            false taggedLink.2) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex =>
          retainedFinalDirectRoutedVariableFullSiteQueries) := by
  let taggedLinks :=
    (canonicalWrappedNormalizedRoutedVariableLinks source).product
      [true, false]
  calc
    taggedLinks.map (fun taggedLink =>
        retainedFinalDirectRoutedVariableClauseQuery
          (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
          false taggedLink.2) =
      taggedLinks.flatMap (fun taggedLink =>
        [retainedFinalDirectRoutedVariableClauseQuery
          (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
          false taggedLink.2]) := by
            rw [← List.map_eq_flatMap]
    _ = taggedLinks.flatMap (fun taggedLink =>
        retainedFinalDirectRoutedVariableQueryBlock
          (normalizedRoutedVariableClauseDescriptor taggedLink)) := by
      apply List.flatMap_congr
      intro taggedLink _taggedLinkMember
      unfold normalizedRoutedVariableClauseDescriptor
      exact
        (retainedFinalDirectRoutedVariableQueryBlock_descriptor_eq
          (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
          taggedLink.2).symm
    _ = (taggedLinks.map normalizedRoutedVariableClauseDescriptor).flatMap
        retainedFinalDirectRoutedVariableQueryBlock := by
      rw [List.flatMap_map]
    _ = ((List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
            (fun _targetIndex => routedVariableFullSiteBlock)).flatMap
        retainedFinalDirectRoutedVariableQueryBlock := by
      rw [canonicalNormalizedRoutedVariableDescriptors_eq_fullSites
        source positiveOffsets]
    _ = (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex =>
          routedVariableFullSiteBlock.flatMap
            retainedFinalDirectRoutedVariableQueryBlock) := by
      rw [List.flatMap_assoc]
    _ = (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex =>
          retainedFinalDirectRoutedVariableFullSiteQueries) := by
      apply List.flatMap_congr
      intro targetIndex _targetIndexMember
      exact routedVariableFullSiteBlock_finalQueryBlock_eq

end LeanTrominoes.PeriodicThreeSATThree
