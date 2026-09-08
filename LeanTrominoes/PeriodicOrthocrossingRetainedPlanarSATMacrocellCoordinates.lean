/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeData

/-! # Canonical macrocell coordinates of retained planar variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Wrapping a macrocell coordinate preserves its strictly interior local
coordinate. Only the drawing-grid coordinate is reduced modulo the period. -/
theorem macrocellCoordinate_emod_period
    (point localCoordinate period : Int)
    (periodPositive : 0 < period)
    (localNonnegative : 0 ≤ localCoordinate)
    (localLt : localCoordinate < planarMacroScale) :
    (planarMacroScale * point + localCoordinate) %
        (planarMacroScale * period) =
      planarMacroScale * (point % period) + localCoordinate := by
  have remainderNonnegative := Int.emod_nonneg point (ne_of_gt periodPositive)
  have remainderLt := Int.emod_lt_of_pos point periodPositive
  have decomposition := Int.emod_add_mul_ediv point period
  have rewritePoint : planarMacroScale * point + localCoordinate =
      (planarMacroScale * (point % period) + localCoordinate) +
        (planarMacroScale * period) * (point / period) := by
    calc
      _ = planarMacroScale * (point % period + period * (point / period)) +
          localCoordinate := congrArg
            (fun value => planarMacroScale * value + localCoordinate)
            decomposition.symm
      _ = _ := by ring
  rw [rewritePoint, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt <;> dsimp [planarMacroScale] at * <;> omega

/-- Grid coordinates of the canonical variable representative. This avoids
performing division at the refined gadget scale. -/
def periodicPlanarSATVariableCanonicalDrawingPoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) : Cell :=
  let point := periodicPlanarSATVariableDrawingPoint formula atom
  let period := drawingGridSize (PeriodicCNF.incidenceGraph formula)
  (point.1 % (period : Int), point.2 % (period : Int))

/-- Every canonically gauged retained variable has its original local gadget
coordinate in the canonically wrapped drawing-grid macrocell. -/
theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_macrocell
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨atom⟩ =
      Cell.add
        (Cell.scale planarMacroScale
          (periodicPlanarSATVariableCanonicalDrawingPoint formula atom))
        (periodicPlanarSATVariableLocalPosition atom) := by
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_mk,
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position]
  change
    ((drawingPeriodicPlanarSATVariablePosition formula atom).1 %
        ((planarMacroScale.toNat *
          drawingGridSize (PeriodicCNF.incidenceGraph formula) : Nat) : Int),
      (drawingPeriodicPlanarSATVariablePosition formula atom).2 %
        ((planarMacroScale.toNat *
          drawingGridSize (PeriodicCNF.incidenceGraph formula) : Nat) : Int)) = _
  rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
  have periodPositive :
      (0 : Int) < drawingGridSize (PeriodicCNF.incidenceGraph formula) :=
    Int.natCast_pos.mpr (drawingGridSize_pos _)
  have localBounds := periodicPlanarSATVariableLocalPosition_in_macrocell atom
  have periodEq :
      ((planarMacroScale.toNat *
        drawingGridSize (PeriodicCNF.incidenceGraph formula) : Nat) : Int) =
      planarMacroScale * drawingGridSize (PeriodicCNF.incidenceGraph formula) := by
    simp [planarMacroScale]
  rw [periodEq]
  apply Prod.ext
  · exact macrocellCoordinate_emod_period _ _ _ periodPositive
      (le_of_lt localBounds.1) localBounds.2.1
  · exact macrocellCoordinate_emod_period _ _ _ periodPositive
      (le_of_lt localBounds.2.2.1) localBounds.2.2.2

/-- For crossing boundaries the canonical-coordinate correction uses the
same ownership quotient already present in the numeric carrier fields. -/
theorem retainedGaugedBoundary_position_eq_ownershipShift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (boundary : CrossingBoundary) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨.boundary boundary⟩ =
      Cell.add
        (Cell.sub (crossingMacroOrigin boundary.crossing)
          (Cell.scale
            (planarMacroScale * drawingGridSize (PeriodicCNF.incidenceGraph formula))
            (crossingRecordPeriodShiftAtPeriod
              (drawingGridSize (PeriodicCNF.incidenceGraph formula))
              boundary.crossing)))
        boundary.side.localPosition := by
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_macrocell]
  have horizontal := Int.emod_add_mul_ediv boundary.crossing.point.1
    (drawingGridSize (PeriodicCNF.incidenceGraph formula))
  have vertical := Int.emod_add_mul_ediv boundary.crossing.point.2
    (drawingGridSize (PeriodicCNF.incidenceGraph formula))
  apply Prod.ext <;>
    dsimp [periodicPlanarSATVariableCanonicalDrawingPoint,
      periodicPlanarSATVariableDrawingPoint,
      periodicPlanarSATVariableLocalPosition, crossingMacroOrigin,
      crossingRecordPeriodShiftAtPeriod, Cell.add, Cell.sub, Cell.scale,
      planarMacroScale] <;>
    nlinarith

end LeanTrominoes.PeriodicOrthocrossing
