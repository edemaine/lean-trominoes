/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeOccurrenceIntrinsicGridSize
import LeanTrominoes.PeriodicPlanarExactOneGridSize
import LeanTrominoes.PeriodicExactOneVariableSupport

/-! # Exact-one grid size measured in the output presentation -/
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
open PeriodicOrthocrossing
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
variable {V : Type} [Primcodable V] [DecidableEq V]
local instance intrinsicGridTargetDecidableEq : DecidableEq (Target V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

omit [Primcodable V] in
theorem final_occurrence_length (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ []) :
    (positioned f).erase.variableOccurrences.length =
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula f).erase.variableOccurrences.length := by
  rw [positioned,retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    PositionedPeriodicCNF.erase_variableGauge,PeriodicCNF.variableOccurrences_variableGauge,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
  exact (PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm _ _).length_eq

omit [Primcodable V] in
theorem source_variables_le_output_size (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ []) :
    f.variableOccurrences.dedup.length ≤ (positioned f).erase.presentationSize := by
  have sourceBound := ThreeOccurrenceGeometry.source_variables_le_output_variables f
  have exactBound := PeriodicOneInThreeNoUnits.composed_variableCount_le
    (ThreeOccurrenceGeometry.formula f).erase
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree f hw)
  rw [← retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase,
    ← final_occurrence_length f hl hw ho hn,PeriodicCNF.variableOccurrences_length] at exactBound
  unfold PeriodicCNF.presentationSize
  omega

theorem drawing_gridSize_le_output_size (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ []) :
    (drawing f).gridSize ≤ 637009920*((positioned f).erase.presentationSize+1) := by
  have periodBound := drawing_gridSize_le_presentationSize f
  have sourceBound := PeriodicCNF.presentationSize_le_variables f ho hn
  have variableBound := source_variables_le_output_size f hl hw ho hn
  omega

end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
