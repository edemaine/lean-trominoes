/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSourceVariableSupport
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableCount
import LeanTrominoes.PeriodicEightOccurrenceSplitExactVariableCount
import LeanTrominoes.PeriodicPlanarThreeOccurrenceGridSize
import LeanTrominoes.PeriodicCNFVariableSizeBounds

/-! # Grid-size bounds measured in the output formula itself -/
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
open PeriodicOrthocrossing
set_option maxHeartbeats 1500000
variable {V : Type} [DecidableEq V]

private theorem support_count_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (xs : List A) (ys : List B) (embedding : A → B) (injective : Function.Injective embedding)
    (support : ∀ a ∈ xs, embedding a ∈ ys) : xs.dedup.length ≤ ys.dedup.length := by
  have nodup := (List.nodup_dedup xs).map injective
  have subset : xs.dedup.map embedding ⊆ ys.dedup := by
    intro a ha
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp ha
    exact List.mem_dedup.mpr (support original (List.mem_dedup.mp originalMember))
  simpa only [List.length_map] using (nodup.subperm subset).length_le

private theorem dedup_length_congr {A : Type*} (xs ys : List A)
    (d e : DecidableEq A) (h : xs=ys) :
    (@List.dedup A d xs).length = (@List.dedup A e ys).length := by
  cases h
  have equal : d=e := Subsingleton.elim _ _
  rw [equal]

theorem source_variables_le_retained (f : PeriodicCNF V) :
    f.variableOccurrences.dedup.length ≤ (retainedPlanarSATFormula f).variableOccurrences.dedup.length := by
  have bound := support_count_bound f.variableOccurrences
    (retainedDrawingPeriodicPlanarSATFormula f).variableOccurrences PeriodicPlanarSATVariable.atom
    (by intro a b h; cases h; rfl) (fun _ ha => retained_periodic_atom_occurs f ha)
  have eq := PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.finalPositionedSource_variableCount_eq_retainedDrawing f
  calc
    _ ≤ _ := bound
    _ = _ := eq.symm
    _ = _ := dedup_length_congr _ _ _ _ rfl

theorem output_variableCount_eq_retained (f : PeriodicCNF V) :
    (formula f).erase.variableOccurrences.dedup.length =
      9*(retainedPlanarSATFormula f).variableOccurrences.dedup.length := by
  rw [formula,retainedFigureNineClearancePositionedFormula,PositionedPeriodicCNF.erase_scale]
  rw [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula,
    (PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm _ _).dedup.length_eq]
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase,
    retainedDrawingEightOccurrenceSplitFormula]
  have result := @PeriodicEightOccurrenceSplit.formula_variableOccurrences_dedup_length
    (WrappedPeriodicPlanarSATVariable V) drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
    (retainedPlanarSATFormula f) (retainedDrawingAngularOccurrencePorts f)
  calc
    _ = _ := dedup_length_congr _ _ _ _ rfl
    _ = _ := result

theorem source_variables_le_output_variables (f : PeriodicCNF V) :
    f.variableOccurrences.dedup.length ≤ (formula f).erase.variableOccurrences.dedup.length := by
  have sourceBound := source_variables_le_retained f
  have countEq := output_variableCount_eq_retained f
  omega

theorem source_variables_le_output_size (f : PeriodicCNF V) :
    f.variableOccurrences.dedup.length ≤ (formula f).erase.presentationSize := by
  have sourceBound := source_variables_le_retained f
  have countEq := output_variableCount_eq_retained f
  have outputBound := (List.dedup_sublist (formula f).erase.variableOccurrences).length_le
  rw [PeriodicCNF.variableOccurrences_length] at outputBound
  unfold PeriodicCNF.presentationSize
  omega

theorem drawing_gridSize_le_output_size (f : PeriodicCNF V)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ []) :
    (drawing f).gridSize ≤ 8847360*((formula f).erase.presentationSize+1) := by
  have periodBound := drawing_period_le_presentationSize f
  have sourceBound := PeriodicCNF.presentationSize_le_variables f ho hn
  have variableBound := source_variables_le_output_size f
  omega

end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
