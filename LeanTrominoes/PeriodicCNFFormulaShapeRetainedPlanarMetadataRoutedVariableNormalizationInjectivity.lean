/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseNormalization
import LeanTrominoes.PeriodicCNFPlanarVariableNormalizationDegree
import LeanTrominoes.PeriodicEqualityGaugeNormalizationInjectivity

/-! # Injectivity of wrapped routed-variable normalization -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Embed a normalized planar-SAT prototype into the opaque wrapped
variable type used by the retained periodic formula. -/
def wrappedPeriodicPlanarSATVariable
    {Variable : Type}
    (node : PeriodicPlanarSATVariable Variable) :
    WrappedPeriodicPlanarSATVariable Variable :=
  ⟨node⟩

theorem wrappedPeriodicPlanarSATVariable_injective
    {Variable : Type} :
    Function.Injective (@wrappedPeriodicPlanarSATVariable Variable) := by
  intro first second equal
  exact congrArg WrappedPeriodicVariable.original equal

/-- The metadata normalization is ordinary external-node normalization
followed by the injective wrapper and the canonical retained gauge. -/
theorem externalWrappedVariableNormalization_eq_gaugeNormalization
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (node : PlanarSATNode Variable) :
    externalWrappedVariableNormalization source node =
      PeriodicEquality.gaugeNormalization
        (normalizePlanarSATNode source.incidenceGraph)
        (@wrappedPeriodicPlanarSATVariable Variable)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source)
        node := by
  cases node with
  | carrier carrier =>
      cases carrier <;> rfl
  | atom atom =>
      rfl

/-- Wrapping and gauging preserve equality of normalized routed-variable
links exactly. -/
theorem routedVariableWrappedNormalizeLink_eq_iff
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : EqualityLink (PlanarSATNode Variable)) :
    PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization source) first =
        PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source) second ↔
      PeriodicEquality.normalizeLink
          (normalizePlanarSATNode source.incidenceGraph) first =
        PeriodicEquality.normalizeLink
          (normalizePlanarSATNode source.incidenceGraph) second := by
  have normalizationEq : externalWrappedVariableNormalization source =
      PeriodicEquality.gaugeNormalization
        (normalizePlanarSATNode source.incidenceGraph)
        (@wrappedPeriodicPlanarSATVariable Variable)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source) := by
    funext node
    exact externalWrappedVariableNormalization_eq_gaugeNormalization
      source node
  rw [normalizationEq]
  exact PeriodicEquality.normalizeLink_gaugeNormalization_eq_iff
    (normalizePlanarSATNode source.incidenceGraph)
    (@wrappedPeriodicPlanarSATVariable Variable)
    wrappedPeriodicPlanarSATVariable_injective
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source)
    first second

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
