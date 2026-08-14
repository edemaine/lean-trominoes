/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingHorizontalCrossings
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-!
# Vertical component of the retained planar-SAT gauge

Nonterminal retained variables already lie in the canonical drawing period.
For terminals, the open vertical-band bound on every horizontal-source route
places the segment endpoint and its strictly interior macrocell coordinate in
the refined fundamental period.  Thus every valid retained variable has
canonical gauge with vertical component zero.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every valid retained planar-SAT variable has zero vertical canonical
position gauge for a horizontal local incidence graph. -/
theorem
    retainedDrawingPeriodicPlanarSATVariableGauge_vertical_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (isLocal : (PeriodicCNF.incidenceGraph formula).IsLocal)
    (horizontal :
      (PeriodicCNF.incidenceGraph formula).HasZeroVerticalOffsets)
    (atom : PeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    ((drawingPeriodicPlanarSATPlacement formula).canonicalPositionGauge
      atom).2 = 0 := by
  cases atom with
  | terminal indexed endpoint =>
      have routeBounds :=
        drawing_routePointsInOpenVerticalBand isLocal horizontal
      have segmentBounds :=
        PeriodicGridDrawing.RoutePointsInOpenVerticalBand.indexedSegment
          routeBounds valid
      have endpointBounds :
          0 < (periodicPlanarSATVariableDrawingPoint formula
              (.terminal indexed endpoint)).2 ∧
            (periodicPlanarSATVariableDrawingPoint formula
              (.terminal indexed endpoint)).2 <
                drawingGridSize (PeriodicCNF.incidenceGraph formula) := by
        cases endpoint with
        | start =>
            simpa [periodicPlanarSATVariableDrawingPoint,
              SegmentTerminal.drawingPoint,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              Cell.add, Cell.scale] using segmentBounds.1
        | finish =>
            simpa [periodicPlanarSATVariableDrawingPoint,
              SegmentTerminal.drawingPoint,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              Cell.add, Cell.scale] using segmentBounds.2
      have localBounds :=
        periodicPlanarSATVariableLocalPosition_in_macrocell
          (Variable := Variable)
          (PeriodicPlanarSATVariable.terminal indexed endpoint)
      change
        (drawingPeriodicPlanarSATVariablePosition formula
          (.terminal indexed endpoint)).2 /
            (drawingPeriodicPlanarSATPlacement formula).period = 0
      rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
      simpa [drawingPeriodicPlanarSATPlacement,
        Cell.add, Cell.scale, planarMacroScale] using
          (macrocellCoordinate_ediv_period_eq_zero
            (drawingGridSize_pos (PeriodicCNF.incidenceGraph formula))
            (le_of_lt endpointBounds.1) endpointBounds.2
            (le_of_lt localBounds.2.2.1) localBounds.2.2.2)
  | boundary boundary =>
      exact congrArg Prod.snd
        (retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
          formula wellFormed (.boundary boundary) valid
          (by intro indexed endpoint unequal; cases unequal))
  | atom sourceAtom =>
      exact congrArg Prod.snd
        (retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
          formula wellFormed (.atom sourceAtom) valid
          (by intro indexed endpoint unequal; cases unequal))
  | crossoverInternal internal =>
      exact congrArg Prod.snd
        (retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
          formula wellFormed (.crossoverInternal internal) valid
          (by intro indexed endpoint unequal; cases unequal))

/-- Wrapping a valid retained variable leaves its zero vertical gauge
component unchanged. -/
theorem retainedDrawingWrappedPeriodicPlanarSATVariableGauge_vertical_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (isLocal : (PeriodicCNF.incidenceGraph formula).IsLocal)
    (horizontal :
      (PeriodicCNF.incidenceGraph formula).HasZeroVerticalOffsets)
    (atom : PeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
      formula ⟨atom⟩).2 = 0 := by
  exact retainedDrawingPeriodicPlanarSATVariableGauge_vertical_eq_zero
    wellFormed isLocal horizontal atom valid

end PeriodicOrthocrossing
end LeanTrominoes
