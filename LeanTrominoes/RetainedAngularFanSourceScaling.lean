import LeanTrominoes.RetainedAngularFanCompleteRoutes
import LeanTrominoes.RetainedAngularTerminalDataScaling

/-!
# Refining the retained source before inserting angular fans

A local Figure 7 fan needs a fixed amount of room around each source
variable and terminal segment.  The right way to create additional global
clearance is to scale the retained source presentation first and only then
insert the fixed-size fan.  In particular, this is different from scaling
the completed fan construction: the source geometry grows by `factor`, while
the local Figure 7 offsets do not.

This file names that composition and proves that positive source scaling
does not alter the angular occurrence order or the resulting logical
fixed-eight formula.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Fixed source-first refinement used to clear the radius-845 retained
terminal corridor before inserting the angular fans. -/
def retainedAngularFanSourceClearanceFactor : Nat :=
  4

@[simp]
theorem retainedAngularFanSourceClearanceFactor_eq :
    retainedAngularFanSourceClearanceFactor = 4 := by
  rfl

theorem retainedAngularFanSourceClearanceFactor_gt_one :
    1 < retainedAngularFanSourceClearanceFactor := by
  native_decide

theorem retainedAngularFanSourceClearanceFactor_pos :
    0 < retainedAngularFanSourceClearanceFactor :=
  lt_trans Nat.zero_lt_one
    retainedAngularFanSourceClearanceFactor_gt_one

theorem retainedAngularFanSourceClearanceFactor_clears_transverseBand :
    845 <
      retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor := by
  native_decide

/-- Insert the retained angular fans after uniformly refining the source
positioned formula, placement, and route family. -/
def retainedAngularFanSourceScaledRefinedFormula
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF (ThreeOccurrenceVariable Variable) :=
  retainedAngularFanRefinedFormula
    (source.scale factor)
    (placement.scale factor)
    (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)

/-- Placement paired with `retainedAngularFanSourceScaledRefinedFormula`. -/
def retainedAngularFanSourceScaledRefinedPlacement
    {Variable : Type*}
    (factor : Nat)
    (placement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement (ThreeOccurrenceVariable Variable) :=
  retainedAngularFanRefinedPlacement
    (placement.scale factor)

/-- Route family obtained by scaling the source first and inserting the
unchanged fixed-size angular fans afterwards. -/
def retainedAngularFanSourceScaledSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedAngularFanSplicedIncidenceRoutes
    (source.scale factor)
    (placement.scale factor)
    (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)

/-- Positive source refinement preserves the exact angular occurrence order
used to assign the eight fan slots. -/
theorem retainedAngularFanSourceScaled_angularOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularOccurrenceOrder (source.scale factor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor routes)).copies atom =
      (angularOccurrenceOrder source.erase routes).copies atom := by
  simp only [PositionedPeriodicCNF.erase_scale,
    angularOccurrenceOrder_copies]
  exact
    angularOccurrenceVariables_scaleIncidenceRoutes
      source.erase factorPositive routes atom

/-- Scaling the source before inserting the fan changes only physical
coordinates, not the logical fixed-eight formula. -/
@[simp]
theorem retainedAngularFanSourceScaledRefinedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedAngularFanSourceScaledRefinedFormula
      factor source placement routes).erase =
      PeriodicEightOccurrenceSplit.formula
        source.erase
        (occurrencePortsOfAngularOrder
          source.erase
          (angularOccurrenceOrder source.erase routes)) := by
  rw [retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula_erase]
  rw [PositionedPeriodicCNF.erase_scale]
  rw [angularOccurrenceOrder_scaleIncidenceRoutes
    source.erase factorPositive routes]

/-- Positive source period and positive source refinement give a positive
period after the fixed-eight fan construction. -/
theorem retainedAngularFanSourceScaledRefinedPlacement_period_pos
    {Variable : Type*}
    {factor : Nat} (factorPositive : 0 < factor)
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period) :
    0 <
      (retainedAngularFanSourceScaledRefinedPlacement
        factor placement).period := by
  apply retainedAngularFanRefinedPlacement_period_pos
  simpa using Nat.mul_pos factorPositive periodPositive

end PeriodicEightOccurrenceSplit
end LeanTrominoes
