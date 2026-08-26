/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizationInjectivity
import LeanTrominoes.PeriodicCNFPlanarAtomNormalizationDegree

/-! # Classification of wrapped normalized routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Read the terminal route index from a wrapped normalized routed-variable
link. -/
def wrappedNormalizedRoutedVariableLinkRouteIndex
    {Variable : Type}
    (link : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable)) : Nat :=
  match link.first.original with
  | .terminal indexed _ => indexed.routeIndex
  | _ => 0

/-- The wrapper and retained gauge leave the first endpoint's route-index
classifier unchanged. -/
@[simp] theorem
    wrappedNormalizedRoutedVariableLinkRouteIndex_normalizeLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink (PlanarSATNode Variable)) :
    wrappedNormalizedRoutedVariableLinkRouteIndex
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source) link) =
      normalizedRoutedVariableLinkRouteIndex
        (PeriodicEquality.normalizeLink
          (normalizePlanarSATNode source.incidenceGraph) link) := by
  have normalizationEq : externalWrappedVariableNormalization source =
      PeriodicEquality.gaugeNormalization
        (normalizePlanarSATNode source.incidenceGraph)
        (@wrappedPeriodicPlanarSATVariable Variable)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source) := by
    funext node
    exact externalWrappedVariableNormalization_eq_gaugeNormalization
      source node
  rw [normalizationEq]
  rfl

/-- On wrapped normalized active variable arms, the route-index classifier
is injective. -/
theorem wrappedNormalizedRoutedVariableLink_eq_of_routeIndex_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {first second : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable)}
    (firstMem : first ∈
      (drawingRoutedVariableLinks source).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source)))
    (secondMem : second ∈
      (drawingRoutedVariableLinks source).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source)))
    (routeIndexEq :
      wrappedNormalizedRoutedVariableLinkRouteIndex first =
        wrappedNormalizedRoutedVariableLinkRouteIndex second) :
    first = second := by
  rcases List.mem_map.mp firstMem with
    ⟨firstSource, firstSourceMem, firstEq⟩
  rcases List.mem_map.mp secondMem with
    ⟨secondSource, secondSourceMem, secondEq⟩
  subst first
  subst second
  have rawFirstMem :
      PeriodicEquality.normalizeLink
          (normalizePlanarSATNode source.incidenceGraph) firstSource ∈
        (drawingRoutedVariableLinks source).map
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode source.incidenceGraph)) :=
    List.mem_map.mpr ⟨firstSource, firstSourceMem, rfl⟩
  have rawSecondMem :
      PeriodicEquality.normalizeLink
          (normalizePlanarSATNode source.incidenceGraph) secondSource ∈
        (drawingRoutedVariableLinks source).map
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode source.incidenceGraph)) :=
    List.mem_map.mpr ⟨secondSource, secondSourceMem, rfl⟩
  have rawRouteIndexEq :
      normalizedRoutedVariableLinkRouteIndex
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode source.incidenceGraph) firstSource) =
        normalizedRoutedVariableLinkRouteIndex
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode source.incidenceGraph) secondSource) := by
    simpa only [
      wrappedNormalizedRoutedVariableLinkRouteIndex_normalizeLink]
      using routeIndexEq
  apply (routedVariableWrappedNormalizeLink_eq_iff
    source firstSource secondSource).mpr
  exact normalizedRoutedVariableLink_eq_of_routeIndex_eq
    source rawFirstMem rawSecondMem rawRouteIndexEq

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
