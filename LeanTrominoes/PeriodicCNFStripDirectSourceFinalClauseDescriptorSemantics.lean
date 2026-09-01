/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockSemantics

/-! # Semantics of complete direct final parent descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseDescriptorSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance
    directFinalClauseDescriptorSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem cycleClauseBlocks_replicate (count : Nat) :
    (List.replicate count FormulaShapeDirectionOrdering.Token.variable).flatMap
        directSourceFinalCycleClauseDescriptorBlock =
      (List.replicate count ()).flatMap fun _ =>
        FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.replicate_succ,
        List.flatMap_cons, List.flatMap_cons]
      rw [show directSourceFinalCycleClauseDescriptorBlock
          FormulaShapeDirectionOrdering.Token.variable =
        FormulaShapeFixedEightDirection.cycleClauseDescriptors by rfl]
      rw [induction]

private theorem cycleRecordBlocks_replicate (count : Nat) :
    (List.replicate count FormulaShapeDirectionOrdering.Token.variable).flatMap
        directFigureNineCycleRouteTailRecordBlock =
      (List.replicate count ()).flatMap fun _ =>
        FormulaShapeRetainedFigureNineCycleTail.localRecordTokens := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.replicate_succ,
        List.flatMap_cons, List.flatMap_cons]
      rw [show directFigureNineCycleRouteTailRecordBlock
          FormulaShapeDirectionOrdering.Token.variable =
        FormulaShapeRetainedFigureNineCycleTail.localRecordTokens by rfl]
      rw [induction]

/-- The independently compiled cycle occurrence suffix is exactly the
descriptor-wise expansion of the repeated nine-clause cycle blocks. -/
theorem directSourceFinalCycleOccurrenceData_eq_clauseDescriptors
    (symbols : List encoding.Γ) :
    directSourceFinalCycleOccurrenceData decider symbols =
      HorizontalRoutedRouteHeaderOccurrenceBlock.output
        (directSourceFinalCycleClauseDescriptors decider symbols) := by
  let count :=
    (PeriodicThreeSATThree.sourceVariables
      (FormulaShapeRetainedFigureNineDirection.sourceScaledForFigureSeven
        (directSourceFormula decider symbols)).erase).length
  have markersEq :
      directRetainedFigureNineFiniteSourceVariableMarkers decider symbols =
        List.replicate count
          FormulaShapeDirectionOrdering.Token.variable := by
    rfl
  have descriptorsEq :
      directSourceFinalCycleClauseDescriptors decider symbols =
        (List.replicate count ()).flatMap fun _ =>
          FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
    unfold directSourceFinalCycleClauseDescriptors
    rw [markersEq]
    exact cycleClauseBlocks_replicate count
  have recordsEq :
      directFigureNineCycleRouteTailRecordTokensCompiled decider symbols =
        (List.replicate count ()).flatMap fun _ =>
          FormulaShapeRetainedFigureNineCycleTail.localRecordTokens := by
    unfold directFigureNineCycleRouteTailRecordTokensCompiled
    rw [markersEq]
    exact cycleRecordBlocks_replicate count
  unfold directSourceFinalCycleOccurrenceData
  rw [recordsEq]
  rw [← FormulaShapeRetainedFigureNineCycleTail.sourceRecordTokens_repeatedCycleBlocks]
  rw [HorizontalRoutedRouteHeaderOccurrenceBlock.occurrenceOutput_batchedRecords_sourceRecordTokens]
  rw [descriptorsEq]

/-- The combined descriptor stream expands to exactly the complete canonical
copied-plus-cycle occurrence order. -/
theorem directSourceFinalClauseDescriptors_occurrenceData_eq
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteHeaderOccurrenceBlock.output
        (directSourceFinalClauseDescriptors decider symbols) =
      directSourceFinalCompiledOccurrenceData decider symbols := by
  rw [directSourceFinalCompiledOccurrenceData_eq_copied_cycle]
  unfold directSourceFinalClauseDescriptors
  rw [show
    HorizontalRoutedRouteHeaderOccurrenceBlock.output
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols ++
          directSourceFinalCycleClauseDescriptors decider symbols) =
      HorizontalRoutedRouteHeaderOccurrenceBlock.output
          (directRetainedFigureNineCopiedClauseDescriptors decider symbols) ++
        HorizontalRoutedRouteHeaderOccurrenceBlock.output
          (directSourceFinalCycleClauseDescriptors decider symbols) by
    simp [HorizontalRoutedRouteHeaderOccurrenceBlock.output]]
  unfold directSourceFinalCopiedOccurrenceData
  rw [← directSourceFinalCycleOccurrenceData_eq_clauseDescriptors]

/-- Consequently the globally parent-indexed local atom-code column is
aligned with every compiled final occurrence. -/
@[simp] theorem directSourceFinalLocalAtomCodes_length_eq_occurrences
    (symbols : List encoding.Γ) :
    (directSourceFinalLocalAtomCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalLocalAtomCodes_length,
    directSourceFinalClauseDescriptors_occurrenceData_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
