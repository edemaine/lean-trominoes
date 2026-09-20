/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeOccurrenceLocality
import LeanTrominoes.PeriodicCNFUnitOffsetBounds

/-! # Unit-radius offsets in the retained source for Figure 9 -/
namespace LeanTrominoes.PeriodicOrthocrossing
set_option maxHeartbeats 1000000
section
local instance offsetBoundsWrappedDecidableEq {V : Type*} [DecidableEq V] : DecidableEq (WrappedPeriodicPlanarSATVariable V) :=
  instDecidableEqWrappedPeriodicVariable

theorem retainedPlanarSATFormula_hasUnitOffsets {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) : (retainedPlanarSATFormula f).HasUnitOffsets := by
  have normalized := PeriodicCNF.anchorNormalize_hasUnitOffsets
    (retained_gauged_formula_isLocal wf degree locality)
  unfold retainedPlanarSATFormula
  rw [retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_eq,
    PositionedPeriodicCNF.erase_deduplicateByLiterals]
  intro clause member
  apply normalized clause
  simpa only [PeriodicCNF.deduplicate,List.mem_dedup,
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_anchorNormalize] using member
end

theorem retainedFigureNineClearancePositionedFormula_hasUnitOffsets {V : Type*} [DecidableEq V]
    {f : PeriodicCNF V} (wf : f.incidenceGraph.IsWellFormed)
    (degree : f.incidenceGraph.DegreeAtMost 3) (locality : f.incidenceGraph.IsLocal) :
    (retainedFigureNineClearancePositionedFormula f).erase.HasUnitOffsets := by
  rw [retainedFigureNineClearancePositionedFormula,PositionedPeriodicCNF.erase_scale]
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_hasUnitOffsets
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
  exact PeriodicEightOccurrenceSplit.formula_hasUnitOffsets _ (retainedPlanarSATFormula_hasUnitOffsets wf degree locality)

end LeanTrominoes.PeriodicOrthocrossing
