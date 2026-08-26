/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierVariableNormalizationData
import LeanTrominoes.PeriodicEqualityGaugeNormalizationInjectivity
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierNormalizationInjectivity

/-! # Injectivity of wrapped retained-carrier normalization -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Embed a normalized carrier prototype into the opaque wrapped planar
variable type. -/
def wrappedPeriodicCarrierNode
    {Variable : Type} (node : PeriodicCarrierNode) :
    WrappedPeriodicPlanarSATVariable Variable :=
  ⟨periodicCarrierNodeToPlanarSATVariable node⟩

theorem wrappedPeriodicCarrierNode_injective
    {Variable : Type} :
    Function.Injective (@wrappedPeriodicCarrierNode Variable) := by
  intro first second equal
  exact periodicCarrierNodeToPlanarSATVariable_injective
    (congrArg WrappedPeriodicVariable.original equal)

/-- The metadata normalization is the ordinary carrier normalization followed
by an injective prototype embedding and the canonical prototype gauge. -/
theorem carrierWrappedVariableNormalization_eq_gaugeNormalization
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (node : CarrierNode) :
    carrierWrappedVariableNormalization source node =
      PeriodicEquality.gaugeNormalization
        (normalizeCarrierNode source.incidenceGraph)
        (@wrappedPeriodicCarrierNode Variable)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData source)
        node := by
  cases node <;>
    rfl

/-- Gauging and wrapping preserve equality of normalized retained carrier
links exactly. -/
theorem carrierWrappedNormalizeLink_eq_iff
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : EqualityLink CarrierNode) :
    PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) first =
        PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source) second ↔
      PeriodicEquality.normalizeLink
          (normalizeCarrierNode source.incidenceGraph) first =
        PeriodicEquality.normalizeLink
          (normalizeCarrierNode source.incidenceGraph) second := by
  have normalizationEq : carrierWrappedVariableNormalization source =
      PeriodicEquality.gaugeNormalization
        (normalizeCarrierNode source.incidenceGraph)
        (@wrappedPeriodicCarrierNode Variable)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData source) := by
    funext node
    exact carrierWrappedVariableNormalization_eq_gaugeNormalization
      source node
  rw [normalizationEq]
  exact PeriodicEquality.normalizeLink_gaugeNormalization_eq_iff
    (normalizeCarrierNode source.incidenceGraph)
    (@wrappedPeriodicCarrierNode Variable)
    wrappedPeriodicCarrierNode_injective
    (retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData source)
    first second

/-- The wrapped, gauged normalized retained-link list is duplicate-free. -/
theorem retainedCarrierWrappedNormalizeLink_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source))).Nodup := by
  apply (retainedDrawingCompleteCarrierLinks_nodup
    source.incidenceGraph).map_on
  intro first firstMem second secondMem wrappedEq
  apply retainedDrawingCompleteCarrierLinks_normalizeLink_injective_on
    firstMem secondMem
  exact (carrierWrappedNormalizeLink_eq_iff source first second).mp wrappedEq

/-- Its two normalized implication clauses are therefore already
duplicate-free. -/
theorem retainedCarrierWrappedNormalizedFormulaClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicEquality.normalizedFormulaClauses
      (carrierWrappedVariableNormalization source)
      (retainedDrawingCompleteCarrierLinks
        source.incidenceGraph)).Nodup := by
  rw [PeriodicEquality.normalizedFormulaClauses_eq]
  exact PeriodicEquality.normalizedClauses_nodup _
    (retainedCarrierWrappedNormalizeLink_nodup source)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
