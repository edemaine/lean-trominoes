/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocality
import LeanTrominoes.PositionedPeriodicCNFLocality
import LeanTrominoes.PeriodicPlanarThreeOccurrenceGeometry

/-! # Manhattan locality of the ordinary planar occurrence-three construction -/
namespace LeanTrominoes.PeriodicOrthocrossing
set_option maxHeartbeats 1000000
section
local instance {V : Type*} [DecidableEq V] : DecidableEq (WrappedPeriodicPlanarSATVariable V) :=
  instDecidableEqWrappedPeriodicVariable

theorem retainedPlanarSATFormula_isLocal {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) : (retainedPlanarSATFormula f).IsLocal := by
  unfold retainedPlanarSATFormula
  rw [retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_eq,
    PositionedPeriodicCNF.deduplicateByLiterals_isLocal_iff]
  apply PositionedPeriodicCNF.anchorNormalize_erase_isLocal
  exact retained_gauged_formula_isLocal wf degree locality

end

theorem retainedFigureNineClearancePositionedFormula_isLocal {V : Type*} [DecidableEq V]
    {f : PeriodicCNF V} (wf : f.incidenceGraph.IsWellFormed)
    (degree : f.incidenceGraph.DegreeAtMost 3) (locality : f.incidenceGraph.IsLocal) :
    (retainedFigureNineClearancePositionedFormula f).erase.IsLocal := by
  rw [retainedFigureNineClearancePositionedFormula,PositionedPeriodicCNF.erase_scale]
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_erase_isLocal
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
  exact PeriodicEightOccurrenceSplit.formula_isLocal _ (retainedPlanarSATFormula_isLocal wf degree locality)

end LeanTrominoes.PeriodicOrthocrossing
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry

theorem isLocal {V : Type} [DecidableEq V] (f : PeriodicCNF V)
    (locality : f.IsLocal) (width : f.WidthAtMost 3) (occurrences : f.OccurrencesAtMost 3) :
    (formula f).erase.IsLocal := by
  apply PeriodicOrthocrossing.retainedFigureNineClearancePositionedFormula_isLocal
  · exact PeriodicCNF.incidenceGraph_isWellFormed f
  · exact PeriodicCNF.incidenceGraph_degreeAtMost width occurrences
  · exact PeriodicCNF.incidenceGraph_isLocal locality

end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
