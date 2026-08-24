/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierVariableNormalizationData

/-! # Numeric normalization semantics of retained carrier pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Numeric period normalization computes exactly the complete wrapped and
canonically gauged offset of every physical carrier node. -/
theorem carrierNodeNormalizationOffsetAtPeriod_eq_wrapped
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (node : CarrierNode) :
    carrierNodeNormalizationOffsetAtPeriod
        (drawingGridSize source.incidenceGraph) node =
      (carrierWrappedVariableNormalization source node).2 := by
  cases node with
  | terminal terminal =>
      simp only [carrierNodeNormalizationOffsetAtPeriod,
        carrierNodeRawNormalizationOffsetAtPeriod,
        carrierNodeNormalizedPrototypePositionAtPeriod]
      rw [segmentTerminalPositionAtPeriod_drawingGridSize]
      simp [carrierWrappedVariableNormalization,
        normalizePlanarSATVariable,
        retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData,
        PeriodicVariablePlacement.canonicalPositionGauge,
        wrappedDrawingPeriodicPlanarSATPlacement,
        drawingPeriodicPlanarSATPlacement,
        drawingPeriodicPlanarSATVariablePosition,
        carrierPositionGaugeAtPeriod, carrierMacroPeriodAtPeriod,
        planarMacroScale]
  | boundary boundary =>
      simp only [carrierNodeNormalizationOffsetAtPeriod,
        carrierNodeRawNormalizationOffsetAtPeriod,
        carrierNodeNormalizedPrototypePositionAtPeriod]
      rw [crossingRecordPeriodNormalizeAtPeriod_drawingGridSize]
      simp [carrierWrappedVariableNormalization,
        normalizePlanarSATVariable,
        retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData,
        PeriodicVariablePlacement.canonicalPositionGauge,
        wrappedDrawingPeriodicPlanarSATPlacement,
        drawingPeriodicPlanarSATPlacement,
        drawingPeriodicPlanarSATVariablePosition,
        carrierPositionGaugeAtPeriod, carrierMacroPeriodAtPeriod,
        planarMacroScale, crossingPeriodShift,
        crossingRecordPeriodShiftAtPeriod,
        CrossingBoundary.periodNormalize]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
