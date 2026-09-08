/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateCompiler

/-! # Canonical terminal coordinates agree with retained gauged placement -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The translation-zero terminal representative has exactly the gauged planar-variable position. -/
theorem carrierNodeCanonicalPositionAtPeriod_terminal_eq_gaugedPosition
    {Variable : Type} [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    carrierNodeCanonicalPositionAtPeriod (drawingGridSize formula.incidenceGraph)
        (.terminal ⟨indexed, (0, 0), endpoint⟩) =
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position ⟨.terminal indexed endpoint⟩ := by
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_mk,
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position]
  unfold carrierNodeCanonicalPositionAtPeriod
  rw [carrierNodePositionAtPeriod_drawingGridSize]
  simp [carrierMacroPeriodAtPeriod, planarMacroScale, CarrierNode.position,
    drawingPeriodicPlanarSATPlacement, drawingPeriodicPlanarSATVariablePosition]

end LeanTrominoes.PeriodicOrthocrossing
