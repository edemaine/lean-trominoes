/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedLinkRouteIndexDedup
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableNodeOrder

/-! # Semantic route indices of routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Read the route index from an active routed-variable endpoint node. -/
def routedVariableNodeRouteIndex
    {Variable : Type} : PlanarSATNode Variable → Nat
  | .carrier (.terminal terminal) => terminal.indexed.routeIndex
  | _ => 0

/-- Normalizing an equality link exposes exactly the route index stored by
its first endpoint node. -/
@[simp] theorem normalizedRoutedVariableLinkRouteIndex_normalizeLink_eq_node
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink (PlanarSATNode Variable)) :
    normalizedRoutedVariableLinkRouteIndex
        (PeriodicEquality.normalizeLink
          (normalizePlanarSATNode source.incidenceGraph) link) =
      routedVariableNodeRouteIndex link.first := by
  rcases link with ⟨first, second, positions⟩
  cases first with
  | carrier carrier =>
      cases carrier <;> rfl
  | atom atom =>
      rfl

/-- The wrapped normalized route-index scan is the exact site-major list of
selected routed-occurrence global edge indices. -/
theorem wrappedNormalizedRoutedVariableRouteIndexScan_eq_occurrenceEdgeIndices
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    wrappedNormalizedRoutedVariableRouteIndexScan source =
      (drawingVariableRouteSites source).flatMap fun site =>
        ((variableRouteOccurrencesAt source site).take 3).map
          CNFRouteOccurrence.edgeIndex := by
  rw [wrappedNormalizedRoutedVariableRouteIndexScan_eq_raw]
  calc
    (drawingRoutedVariableLinks source).map (fun link =>
        normalizedRoutedVariableLinkRouteIndex
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode source.incidenceGraph) link)) =
      (drawingRoutedVariableLinks source).map (fun link =>
        routedVariableNodeRouteIndex link.first) := by
          apply List.map_congr_left
          intro link _linkMember
          exact
            normalizedRoutedVariableLinkRouteIndex_normalizeLink_eq_node
              source link
    _ = ((drawingRoutedVariableLinks source).map
          EqualityLink.first).map routedVariableNodeRouteIndex := by
          simp [List.map_map, Function.comp_def]
    _ = ((drawingVariableRouteSites source).flatMap fun site =>
          (routedVariableNodes source site).take 3).map
            routedVariableNodeRouteIndex := by
          rw [drawingRoutedVariableLinks_firsts]
    _ = (drawingVariableRouteSites source).flatMap (fun site =>
          ((routedVariableNodes source site).take 3).map
            routedVariableNodeRouteIndex) := by
          rw [List.map_flatMap]
    _ = (drawingVariableRouteSites source).flatMap fun site =>
        ((variableRouteOccurrencesAt source site).take 3).map
          CNFRouteOccurrence.edgeIndex := by
          apply List.flatMap_congr
          intro site _siteMember
          rw [routedVariableNodes_eq_map_targetTerminals]
          simp [List.map_take, List.map_map, Function.comp_def,
            routedVariableNodeRouteIndex,
            CNFRouteOccurrence.targetTerminal]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
