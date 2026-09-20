/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarExactOneEndpoint
import LeanTrominoes.PeriodicPlanarThreeOccurrenceGridSize

/-! # A linear grid-size bound for the planar exact-one construction -/
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
open PeriodicOrthocrossing
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
variable {V : Type} [Primcodable V] [DecidableEq V]
local instance gridSizeTargetDecidableEq : DecidableEq (Target V) := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

omit [Primcodable V] in
theorem placement_period_eq (f : PeriodicCNF V) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement f).period =
      72 * (ThreeOccurrenceGeometry.placement f).period := by
  simp only [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    PeriodicVariablePlacement.variableGauge_period,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
    PeriodicOneInThreeNoUnitsPositioned.placement,PeriodicOneInThreePositioned.placement,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,PlanarOneInThree.gadgetScale]
  change 6*(12*(ThreeOccurrenceGeometry.placement f).period) = _
  ring

theorem drawing_gridSize_le_presentationSize (f : PeriodicCNF V) :
    (drawing f).gridSize ≤ 53084160 * (2*f.presentationSize+1) := by
  unfold drawing
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize _ _ _
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_pos f),
    placement_period_eq]
  have h := ThreeOccurrenceGeometry.period_le_presentationSize f
  omega

end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
