/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierPairNormalizationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNextSliceData

/-! # Numeric next-slice semantics of retained carrier pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The graph-free pair-relative offset is exactly the normalized relative
offset used by the retained carrier descriptor. -/
theorem carrierNodePairRelativeOffsetAtPeriod_eq_normalizeLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (pair : CarrierNode × CarrierNode) :
    carrierNodePairRelativeOffsetAtPeriod
        (drawingGridSize source.incidenceGraph) pair =
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source)
        (carrierNodePairLink source.incidenceGraph pair)).relativeOffset := by
  unfold carrierNodePairRelativeOffsetAtPeriod
    PeriodicEquality.normalizeLink carrierNodePairLink
  rw [carrierNodeNormalizationOffsetAtPeriod_eq_wrapped,
    carrierNodeNormalizationOffsetAtPeriod_eq_wrapped]

/-- The numeric next-slice bit of an endpoint pair equals the existing
formula-level bit of its semantic positioned carrier link. -/
theorem carrierNodePairNextSliceAtPeriod_eq_carrierLinkNextSlice
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (pair : CarrierNode × CarrierNode) :
    carrierNodePairNextSliceAtPeriod
        (drawingGridSize source.incidenceGraph) pair =
      carrierLinkNextSlice source
        (carrierNodePairLink source.incidenceGraph pair) := by
  unfold carrierNodePairNextSliceAtPeriod carrierLinkNextSlice
  rw [carrierNodePairRelativeOffsetAtPeriod_eq_normalizeLink]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
