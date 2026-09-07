/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDirectionBlocks
import LeanTrominoes.PeriodicCNFStripHorizontalClauseFanDirectionBlockSemantics

/-! # Direct clause frames agree with the horizontal semantic fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open HorizontalRoutedRouteHeaderClauseFrame

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance clauseFanSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every direct clause fan is the executable horizontal fan at the same
actual clause index, including all three terminal directions. -/
theorem directSourceFinalClauseFans_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalClauseFans decider symbols =
      (List.range (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.length).map
          (fun index => horizontalOccurrenceClauseRibbonFanDataComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, index)) := by
  rw [directSourceFinalClauseFans_eq_horizontalDirectionBlocks]
  exact horizontalClauseIncomingDirectionBlocks_fans_eq_computed _

/-- The two clause-frame fields agree jointly, block by block, with the
horizontal fan at the clause index and the group at the literal index. -/
theorem directSourceFinalClauseFrameBlocks_fan_groups_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrameBlocks decider symbols).map
        (List.map fun frame => (frame.clauseFan, frame.group)) =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.zipIdx.map
          (fun clause => (List.range clause.1.literals.length).map fun index =>
            (horizontalOccurrenceClauseRibbonFanDataComputed
              (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, clause.2),
              terminalGroupOfLiteralIndex index)) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  let blocks := directSourceFinalClauseFrameBlocks decider symbols
  let clauses := (horizontalRoutedFormulaComputed source).clauses
  let fan := fun index => horizontalOccurrenceClauseRibbonFanDataComputed (source, index)
  have fans : blocks.map blockFan = clauses.zipIdx.map (fun clause => fan clause.2) := by
    change directSourceFinalClauseFans decider symbols = _
    rw [directSourceFinalClauseFans_eq_horizontal]
    change (List.range clauses.length).map fan = clauses.zipIdx.map (fan ∘ Prod.snd)
    rw [← List.map_map, List.zipIdx_map_snd, ← List.range_eq_range']
  have lengths : blocks.map List.length =
      clauses.zipIdx.map (fun clause => clause.1.literals.length) := by
    have actual := directSourceFinalClauseFrameBlocks_lengths_eq_horizontalRouted decider symbols
    have actualLengths : blocks.map List.length =
        clauses.map (fun clause => clause.literals.length) := by
      simpa only [PositionedPeriodicCNF.erase, List.map_map, Function.comp_def] using actual
    rw [actualLengths]
    change clauses.map (fun clause => clause.literals.length) =
      clauses.zipIdx.map ((fun clause => clause.literals.length) ∘ Prod.fst)
    rw [← List.map_map, List.zipIdx_map_fst]
  have paired := congrArg₂ List.zip fans lengths
  rw [List.zip_map', List.zip_map'] at paired
  have fields := congrArg
    (List.map fun pair : ClauseRibbonFanData × Nat =>
      (List.range pair.2).map fun index => (pair.1, terminalGroupOfLiteralIndex index)) paired
  have blockFields : blocks.map (List.map fun frame => (frame.clauseFan, frame.group)) =
      blocks.map (fun block => (List.range block.length).map fun index =>
        (blockFan block, terminalGroupOfLiteralIndex index)) := by
    apply List.map_congr_left
    intro block member
    exact outputBlock_fan_groups (directSourceFinalClauseDescriptors decider symbols) block member
  rw [show (directSourceFinalClauseFrameBlocks decider symbols).map
      (List.map fun frame => (frame.clauseFan, frame.group)) = _ from blockFields]
  simpa only [List.map_map, Function.comp_def] using fields

/-- Forgetting the proof-side block boundaries gives the complete horizontal
clause endpoint fields in clause-major, literal-minor occurrence order. -/
theorem directSourceFinalClauseFrames_fan_groups_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrames decider symbols).map
        (fun frame => (frame.clauseFan, frame.group)) =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.zipIdx.flatMap
          (fun clause => (List.range clause.1.literals.length).map fun index =>
            (horizontalOccurrenceClauseRibbonFanDataComputed
              (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, clause.2),
              terminalGroupOfLiteralIndex index)) := by
  have fields := congrArg List.flatten
    (directSourceFinalClauseFrameBlocks_fan_groups_eq_horizontal decider symbols)
  rw [← List.map_flatten, directSourceFinalClauseFrameBlocks_flatten,
    List.flatten_eq_flatMap, List.flatMap_map] at fields
  simpa only [id_eq] using fields

end LeanTrominoes.PeriodicCNFStripReduction

end
