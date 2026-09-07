/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteDirectionSemantics

/-! # Direct parent descriptors agree with the actual Figure 9 source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open FormulaShapeDirectionOrdering
open FormulaShapeRetainedFigureNineDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance descriptorSourceStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance descriptorSourceVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem cycleMarkers_flatMap {α : Type} (values : List α) :
    (List.replicate values.length Token.variable).flatMap
        directSourceFinalCycleClauseDescriptorBlock =
      values.flatMap (fun _ => FormulaShapeFixedEightDirection.cycleClauseDescriptors) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.length_cons, List.replicate_succ, List.flatMap_cons, ih]
      rfl

theorem directSourceFinalCycleClauseDescriptors_eq_finiteCycle
    (symbols : List encoding.Γ) :
    directSourceFinalCycleClauseDescriptors decider symbols =
      finiteCycleClauseDescriptors (directSourceFormula decider symbols) := by
  unfold directSourceFinalCycleClauseDescriptors
    directRetainedFigureNineFiniteSourceVariableMarkers finiteCycleClauseDescriptors
    directSourceFormula
  exact cycleMarkers_flatMap _

/-- The actual source's descriptor stream is the compiled parent-clause list
followed only by variable markers, which every occurrence compiler ignores. -/
theorem directSourceFinalClauseDescriptors_eq_source_prefix
    (symbols : List encoding.Γ) :
    descriptors (directSourceFormula decider symbols) =
      directSourceFinalClauseDescriptors decider symbols ++
        List.replicate
          (PeriodicOrthocrossing.retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
            (directSourceFormula decider symbols)).erase.variableOccurrences.dedup.length
          Token.variable := by
  have occurrences :
      @PeriodicCNF.OccurrencesAtMost Variable
        (@instBEqOfDecidableEq Variable descriptorSourceVariableDecidableEq)
        (by infer_instance) 3 (directSourceFormula decider symbols) := by
    exact PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree (PolySpaceCompiler.formulaOfSymbols decider symbols))
  rw [@descriptors_eq_finiteDescriptors Variable descriptorSourceVariableDecidableEq
    (directSourceFormula decider symbols)
    (sourceFormula_isLocal (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_widthAtMostThree (PolySpaceCompiler.formulaOfSymbols decider symbols))
    occurrences
    (sourceFormula_clausesNonempty (PolySpaceCompiler.formulaOfSymbols decider symbols))]
  unfold finiteDescriptors directSourceFinalClauseDescriptors
  rw [← directSourceFinalCycleClauseDescriptors_eq_finiteCycle]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
