/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceParentClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseElementDegreeSemantics

/-! # Exact clause boundaries in the direct finite frame stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance clauseFrameBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The existing frame stream with its final-clause boundaries retained. -/
def directSourceFinalClauseFrameBlocks (symbols : List encoding.Γ) :
    List (List FinalClauseFrame) :=
  HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
    (directSourceFinalClauseDescriptors decider symbols)

@[simp] theorem directSourceFinalClauseFrameBlocks_flatten
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrameBlocks decider symbols).flatten =
      directSourceFinalClauseFrames decider symbols := by
  exact HorizontalRoutedRouteHeaderClauseFrame.outputBlocks_flatten _

/-- Each final clause is binary or ternary, so its fan's right-terminal bit
determines its arity exactly. -/
theorem directSourceFinalClauseFrameBlocks_lengths_eq_fans
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrameBlocks decider symbols).map List.length =
      (directSourceFinalClauseFans decider symbols).map
        (fun fan => if fan.hasRight then 3 else 2) := by
  change _ = ((directSourceFinalClauseFrameBlocks decider symbols).map
    HorizontalRoutedRouteHeaderClauseFrame.blockFan).map _
  rw [List.map_map]
  apply List.map_congr_left
  intro block blockMember
  have kinds := (finalClauseFrameBlocks_spec
    (directSourceFinalClauseDescriptors decider symbols) block blockMember).2
  have sizes := congrArg List.length kinds
  cases rightEq : (HorizontalRoutedRouteHeaderClauseFrame.blockFan block).hasRight <;>
    simpa [finalClauseTerminalConnectorKinds, finalClauseFrameBlockFan, rightEq] using sizes

/-- Frame blocks have exactly the arities of the actual horizontal typed
source, in clause order. -/
theorem directSourceFinalClauseFrameBlocks_lengths_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrameBlocks decider symbols).map List.length =
      (horizontalThreeDMTypedSourceComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.map List.length := by
  rw [directSourceFinalClauseFrameBlocks_lengths_eq_fans]
  have bits := directSourceFinalClauseFans_hasRight_eq_typedClauseTernary
    decider symbols
  have lengths := congrArg (List.map fun right : Bool => if right then 3 else 2) bits
  simp only [List.map_map, Function.comp_def] at lengths
  rw [lengths]
  apply List.map_congr_left
  intro clause clauseMember
  rcases horizontalThreeDMTypedSourceComputed_arityTwoOrThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols) clause clauseMember with two | three
  · simp only [two, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, if_false]
  · simp only [three, decide_true, if_true]

/-- Padding and anchor normalization preserve these same clause boundaries
in the stored routed presentation. -/
theorem directSourceFinalClauseFrameBlocks_lengths_eq_horizontalRouted
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrameBlocks decider symbols).map List.length =
      (horizontalRoutedFormulaComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.map List.length := by
  rw [directSourceFinalClauseFrameBlocks_lengths_eq_horizontalTyped,
    horizontalThreeDMTypedSourceComputed_clauseLengths_eq_horizontalFormula,
    horizontalRoutedFormulaComputed_clauseLengths_eq_horizontalFormula]

end LeanTrominoes.PeriodicCNFStripReduction

end
