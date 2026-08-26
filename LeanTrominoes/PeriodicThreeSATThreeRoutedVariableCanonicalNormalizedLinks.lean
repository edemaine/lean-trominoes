/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableNormalizedLinkOrder

/-! # Canonical normalized routed-variable links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Normalize the final-site active links of each positional occurrence, in
rotated target order. -/
def canonicalWrappedNormalizedRoutedVariableLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))) :=
  (rotatedOccurrenceVariables source).flatMap fun atom =>
    (routedVariableLinksAt
        (formula source) (atom, (1, 1))).map
      (PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization (formula source)))

/-- Normalized active links at one site expose the route indices of the
selected routed occurrences in the same order. -/
theorem normalizedRoutedVariableLinksAt_routeIndices_eq_edgeIndices
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    ((routedVariableLinksAt formula site).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization formula))).map
        wrappedNormalizedRoutedVariableLinkRouteIndex =
      ((variableRouteOccurrencesAt formula site).take 3).map
        CNFRouteOccurrence.edgeIndex := by
  rw [List.map_map]
  calc
    (routedVariableLinksAt formula site).map
        (wrappedNormalizedRoutedVariableLinkRouteIndex ∘
          PeriodicEquality.normalizeLink
            (externalWrappedVariableNormalization formula)) =
      (routedVariableLinksAt formula site).map
        (fun link => routedVariableNodeRouteIndex link.first) := by
          apply List.map_congr_left
          intro link _linkMember
          simp only [Function.comp_apply,
            wrappedNormalizedRoutedVariableLinkRouteIndex_normalizeLink,
            normalizedRoutedVariableLinkRouteIndex_normalizeLink_eq_node]
    _ = ((routedVariableLinksAt formula site).map
          EqualityLink.first).map routedVariableNodeRouteIndex := by
          simp [List.map_map, Function.comp_def]
    _ = ((routedVariableNodes formula site).take 3).map
          routedVariableNodeRouteIndex := by
          have firsts :
              (routedVariableLinksAt formula site).map
                  EqualityLink.first =
                (routedVariableNodes formula site).take 3 := by
            unfold routedVariableLinksAt equalityTakeThreeLinks
            rw [List.map_map]
            change ((routedVariableNodes formula site).take 3).zipIdx.map
                Prod.fst =
              (routedVariableNodes formula site).take 3
            exact List.zipIdx_map_fst 0 _
          rw [firsts]
    _ = ((variableRouteOccurrencesAt formula site).take 3).map
          CNFRouteOccurrence.edgeIndex := by
          rw [routedVariableNodes_eq_map_targetTerminals]
          simp [List.map_take, List.map_map, Function.comp_def,
            routedVariableNodeRouteIndex,
            CNFRouteOccurrence.targetTerminal]

/-- The canonical final-site normalized links expose exactly the canonical
edge-index scan. -/
theorem canonicalWrappedNormalizedRoutedVariableLinks_routeIndices_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (canonicalWrappedNormalizedRoutedVariableLinks source).map
        wrappedNormalizedRoutedVariableLinkRouteIndex =
      canonicalRoutedVariableEdgeIndexScan source := by
  unfold canonicalWrappedNormalizedRoutedVariableLinks
    canonicalRoutedVariableEdgeIndexScan
    routedVariableFinalSiteEdgeIndexBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro atom _atomMember
  exact normalizedRoutedVariableLinksAt_routeIndices_eq_edgeIndices
    (formula source) (atom, (1, 1))

/-- Every canonical final-site normalized link already occurs in the raw
normalized routed-variable link stream. -/
theorem canonicalWrappedNormalizedRoutedVariableLinks_subset_raw
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    canonicalWrappedNormalizedRoutedVariableLinks source ⊆
      (drawingRoutedVariableLinks (formula source)).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization (formula source))) := by
  intro normalizedLink normalizedLinkMember
  unfold canonicalWrappedNormalizedRoutedVariableLinks at normalizedLinkMember
  rcases List.mem_flatMap.mp normalizedLinkMember with
    ⟨atom, atomMember, normalizedLinkMember⟩
  rcases List.mem_map.mp normalizedLinkMember with
    ⟨link, linkMember, rfl⟩
  apply List.mem_map.mpr
  refine ⟨link, ?_, rfl⟩
  unfold drawingRoutedVariableLinks
  apply List.mem_flatMap.mpr
  refine ⟨(atom, (1, 1)), ?_, linkMember⟩
  rw [drawingVariableRouteSites_formula_eq_boundary_append_rotated
    source positiveOffsets]
  apply List.mem_append.mpr
  right
  unfold rotatedVariableRouteSiteBlocks
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  simp [variableRouteSiteBlock, neighborTranslations,
    neighborCoordinates, Cell.add]

/-- Stable deduplication of normalized routed-variable links is exactly the
final-site list in rotated occurrence order. -/
theorem deduplicatedWrappedNormalizedRoutedVariableLinks_formula_eq_canonical
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    deduplicatedWrappedNormalizedRoutedVariableLinks (formula source) =
      canonicalWrappedNormalizedRoutedVariableLinks source := by
  let raw := (drawingRoutedVariableLinks (formula source)).map
    (PeriodicEquality.normalizeLink
      (externalWrappedVariableNormalization (formula source)))
  have deduplicatedSubset :
      deduplicatedWrappedNormalizedRoutedVariableLinks
          (formula source) ⊆ raw := by
    intro link linkMember
    exact List.mem_dedup.mp linkMember
  have canonicalSubset :
      canonicalWrappedNormalizedRoutedVariableLinks source ⊆ raw :=
    canonicalWrappedNormalizedRoutedVariableLinks_subset_raw
      source positiveOffsets
  have routeIndicesEq :
      (deduplicatedWrappedNormalizedRoutedVariableLinks
          (formula source)).map
          wrappedNormalizedRoutedVariableLinkRouteIndex =
        (canonicalWrappedNormalizedRoutedVariableLinks source).map
          wrappedNormalizedRoutedVariableLinkRouteIndex := by
    rw [
      deduplicatedWrappedNormalizedRoutedVariableLinks_formula_routeIndices_eq
        source positiveOffsets,
      canonicalWrappedNormalizedRoutedVariableLinks_routeIndices_eq]
  have listEq : ∀
      (first second : List (PeriodicEquality.NormalizedLink
        (WrappedPeriodicPlanarSATVariable
          (ThreeOccurrenceVariable Variable)))),
      first ⊆ raw → second ⊆ raw →
      first.map wrappedNormalizedRoutedVariableLinkRouteIndex =
        second.map wrappedNormalizedRoutedVariableLinkRouteIndex →
      first = second := by
    intro first
    induction first with
    | nil =>
        intro second _firstSubset _secondSubset mapped
        cases second with
        | nil => rfl
        | cons second tail => simp at mapped
    | cons first rest induction =>
        intro second firstSubset secondSubset mapped
        cases second with
        | nil =>
            simp at mapped
        | cons second tail =>
            simp only [List.map_cons, List.cons.injEq] at mapped
            have firstMember : first ∈ raw :=
              firstSubset (by simp)
            have secondMember : second ∈ raw :=
              secondSubset (by simp)
            have firstEqSecond :=
              wrappedNormalizedRoutedVariableLink_eq_of_routeIndex_eq
                (formula source) firstMember secondMember mapped.1
            subst second
            apply congrArg (List.cons first)
            apply induction tail
            · intro link linkMember
              exact firstSubset (by simp [linkMember])
            · intro link linkMember
              exact secondSubset (by simp [linkMember])
            · exact mapped.2
  exact listEq _ _ deduplicatedSubset canonicalSubset routeIndicesEq

end PeriodicThreeSATThree
end LeanTrominoes
