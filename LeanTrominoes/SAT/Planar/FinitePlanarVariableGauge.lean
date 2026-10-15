/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.FiniteOrthocrossingBounds
import LeanTrominoes.SAT.CNF.FiniteCNFIncidenceOffsets
import LeanTrominoes.Graphs.Drawings.Orthogonal.Retained.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-! # Valid planar variables of finite sources have zero canonical gauge -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PlanarThreeSAT

theorem retainedVariableGauge_zero_of_source_zero
    {V : Type*} [DecidableEq V] (formula : PeriodicCNF V)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets formula)
    (atom : PeriodicPlanarSATVariable V) (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    (drawingPeriodicPlanarSATPlacement formula).canonicalPositionGauge atom=(0,0) := by
  cases atom with
  | terminal indexed endpoint =>
    have endpoints := drawing_indexedSegment_endpoints_inFundamental_of_zero wellFormed degree
      (FiniteCNF.incidenceGraph_zero formula zero) valid
    have drawingPointBounds : InFundamentalDrawingSquare formula.incidenceGraph
        (periodicPlanarSATVariableDrawingPoint formula (.terminal indexed endpoint)) := by
      cases endpoint with
      | start =>
        simpa [periodicPlanarSATVariableDrawingPoint,SegmentTerminal.drawingPoint,
          GridSegment.translate,PeriodicGridDrawing.periodTranslation,Cell.add,Cell.scale] using endpoints.1
      | finish =>
        simpa [periodicPlanarSATVariableDrawingPoint,SegmentTerminal.drawingPoint,
          GridSegment.translate,PeriodicGridDrawing.periodTranslation,Cell.add,Cell.scale] using endpoints.2
    have localBounds := periodicPlanarSATVariableLocalPosition_in_macrocell
      (Variable := V) (.terminal indexed endpoint)
    have periodPositive := drawingGridSize_pos formula.incidenceGraph
    apply Prod.ext
    · change (drawingPeriodicPlanarSATVariablePosition formula (.terminal indexed endpoint)).1 /
        (drawingPeriodicPlanarSATPlacement formula).period=0
      rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
      simpa [drawingPeriodicPlanarSATPlacement,Cell.add,Cell.scale,planarMacroScale] using
        (macrocellCoordinate_ediv_period_eq_zero periodPositive drawingPointBounds.1 drawingPointBounds.2.1
          (le_of_lt localBounds.1) localBounds.2.1)
    · change (drawingPeriodicPlanarSATVariablePosition formula (.terminal indexed endpoint)).2 /
        (drawingPeriodicPlanarSATPlacement formula).period=0
      rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
      simpa [drawingPeriodicPlanarSATPlacement,Cell.add,Cell.scale,planarMacroScale] using
        (macrocellCoordinate_ediv_period_eq_zero periodPositive drawingPointBounds.2.2.1 drawingPointBounds.2.2.2
          (le_of_lt localBounds.2.2.1) localBounds.2.2.2)
  | boundary boundary =>
    exact retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal formula wellFormed _ valid
      (fun _ _ eq => by cases eq)
  | atom atom =>
    exact retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal formula wellFormed _ valid
      (fun _ _ eq => by cases eq)
  | crossoverInternal internal =>
    exact retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal formula wellFormed _ valid
      (fun _ _ eq => by cases eq)

end LeanTrominoes.PeriodicOrthocrossing
