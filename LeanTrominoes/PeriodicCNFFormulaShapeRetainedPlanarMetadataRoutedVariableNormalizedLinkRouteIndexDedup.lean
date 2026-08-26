/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizationClassification
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedFamilyDeduplication

/-! # Route-index keys of deduplicated routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Route-index keys of the wrapped normalized links, before stable
deduplication and in exact routed-variable presentation order. -/
def wrappedNormalizedRoutedVariableRouteIndexScan
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  (drawingRoutedVariableLinks source).map fun link =>
    wrappedNormalizedRoutedVariableLinkRouteIndex
      (PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization source) link)

/-- Wrapping and gauging do not change the route-index scan. -/
theorem wrappedNormalizedRoutedVariableRouteIndexScan_eq_raw
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    wrappedNormalizedRoutedVariableRouteIndexScan source =
      (drawingRoutedVariableLinks source).map fun link =>
        normalizedRoutedVariableLinkRouteIndex
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode source.incidenceGraph) link) := by
  unfold wrappedNormalizedRoutedVariableRouteIndexScan
  apply List.map_congr_left
  intro link _linkMember
  exact
    wrappedNormalizedRoutedVariableLinkRouteIndex_normalizeLink source link

/-- Mapping the deduplicated wrapped links to route indices is exactly
stable deduplication of the original route-index scan. -/
theorem
    deduplicatedWrappedNormalizedRoutedVariableLinks_routeIndices_eq_scan_dedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (deduplicatedWrappedNormalizedRoutedVariableLinks source).map
        wrappedNormalizedRoutedVariableLinkRouteIndex =
      (wrappedNormalizedRoutedVariableRouteIndexScan source).dedup := by
  let links := (drawingRoutedVariableLinks source).map
    (PeriodicEquality.normalizeLink
      (externalWrappedVariableNormalization source))
  have injectiveOn : ∀ first ∈ links, ∀ second ∈ links,
      wrappedNormalizedRoutedVariableLinkRouteIndex first =
        wrappedNormalizedRoutedVariableLinkRouteIndex second →
      first = second := by
    intro first firstMember second secondMember routeIndexEq
    exact wrappedNormalizedRoutedVariableLink_eq_of_routeIndex_eq
      source firstMember secondMember routeIndexEq
  have commute := List.dedup_map_of_injective_on
    wrappedNormalizedRoutedVariableLinkRouteIndex links injectiveOn
  change links.dedup.map
      wrappedNormalizedRoutedVariableLinkRouteIndex =
    ((drawingRoutedVariableLinks source).map (fun link =>
      wrappedNormalizedRoutedVariableLinkRouteIndex
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source) link))).dedup
  have scanEq :
      (drawingRoutedVariableLinks source).map (fun link =>
          wrappedNormalizedRoutedVariableLinkRouteIndex
            (PeriodicEquality.normalizeLink
              (externalWrappedVariableNormalization source) link)) =
        links.map wrappedNormalizedRoutedVariableLinkRouteIndex := by
    unfold links
    rw [List.map_map]
    rfl
  rw [scanEq]
  exact commute.symm

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
