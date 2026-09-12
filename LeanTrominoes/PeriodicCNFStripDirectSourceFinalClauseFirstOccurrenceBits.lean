/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFanHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceArity
import LeanTrominoes.UnaryFieldFirstBlockFilter

/-! # One finite control bit for the first occurrence of every actual clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicPlanarOneInThreeToThreeDM
open UnaryFieldBooleanFilter

private theorem terminalGroup_top_iff (index : Nat) :
    terminalGroupOfLiteralIndex index = .top ↔ index = 0 := by
  cases index with
  | zero => simp [terminalGroupOfLiteralIndex]
  | succ index => cases index <;> simp [terminalGroupOfLiteralIndex]

private theorem positionedClause_length_pos {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (clause : PositionedPeriodicClause Variable) (member : clause ∈ source.clauses) :
    0 < clause.literals.length := by
  have erasedMember : clause.literals ∈ source.erase.clauses := List.mem_map.mpr ⟨clause, member, rfl⟩
  rcases arity clause.literals erasedMember with two | three <;> omega

/-- Every actual routed clause has at least one literal. -/
theorem horizontalRoutedClause_length_pos (source : PeriodicCNF Nat)
    (clause : PositionedPeriodicClause RoutedVariable)
    (member : clause ∈ (horizontalRoutedFormulaComputed source).clauses) : 0 < clause.literals.length := by
  have arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree (horizontalRoutedFormulaComputed source).erase := by
    rw [horizontalRoutedFormulaComputed_eq_semanticData]
    exact horizontalSemanticRoutedFormula_arityTwoOrThreeComputed source
  exact positionedClause_length_pos _ arity clause member

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Only the top terminal is the first occurrence of its actual clause. -/
def directSourceFinalClauseFirstBits (symbols : List encoding.Γ) : List Bool :=
  (directSourceFinalClauseFrames decider symbols).flatMap fun frame => [decide (frame.group = .top)]

noncomputable def directSourceFinalClauseFirstBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalClauseFirstBits decider) := by
  let mapped := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFramesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      (fun frame : HorizontalRoutedRouteHeaderClauseFrame.Data => [decide (frame.group = .top)]))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq mapped (fun _ => rfl)

theorem directSourceFinalClauseFirstBits_eq_horizontal (symbols : List encoding.Γ) :
    directSourceFinalClauseFirstBits decider symbols =
      (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.flatMap
        (fun clause => firstBlockControls clause.literals.length) := by
  have identified := congrArg (List.map fun pair : ClauseRibbonFanData × PlanarThreeDM.X3CClauseTerminalGroup =>
    decide (pair.2 = .top)) (directSourceFinalClauseFrames_fan_groups_eq_horizontal decider symbols)
  simp only [List.map_map, List.map_flatMap, Function.comp_def, terminalGroup_top_iff] at identified
  unfold directSourceFinalClauseFirstBits
  rw [← List.map_eq_flatMap]
  refine identified.trans ?_
  unfold firstBlockControls
  exact PeriodicCNF.zipIdx_flatMap_fst
    (fun clause : PositionedPeriodicClause RoutedVariable =>
      (List.range clause.literals.length).map (fun index => decide (index = 0)))
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses 0

end LeanTrominoes.PeriodicCNFStripReduction
end
