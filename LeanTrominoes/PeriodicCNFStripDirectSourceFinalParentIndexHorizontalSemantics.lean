/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceParentIndex
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceParentClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseElementDegreeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceEntryOrder
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexPermutation

/-! # Compiled parent indices are the actual horizontal clause positions -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem directSourceFinalClauseFrameBlockLengths_eq_fanArities
    (symbols : List encoding.Γ) :
    (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
        (directSourceFinalClauseDescriptors decider symbols)).map List.length =
      (directSourceFinalClauseFans decider symbols).map
        (fun fan => if fan.hasRight then 3 else 2) := by
  rw [directSourceFinalClauseFans_eq_blockFans, List.map_map]
  apply List.map_congr_left
  intro block member
  have lengths := congrArg List.length
    (finalClauseFrameBlocks_spec (directSourceFinalClauseDescriptors decider symbols) block member).2
  by_cases right : (finalClauseFrameBlockFan block).hasRight
  · simpa [finalClauseTerminalConnectorKinds, right] using lengths
  · simpa [finalClauseTerminalConnectorKinds, right] using lengths

private theorem directSourceFinalClauseFanArities_eq_typedLengths
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFans decider symbols).map
        (fun fan => if fan.hasRight then 3 else 2) =
      (horizontalThreeDMTypedSourceComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.map List.length := by
  have lifted := congrArg (List.map (fun flag : Bool => if flag then 3 else 2))
    (directSourceFinalClauseFans_hasRight_eq_typedClauseTernary decider symbols)
  simp only [List.map_map, Function.comp_def] at lifted
  refine lifted.trans ?_
  apply List.map_congr_left
  intro clause member
  rcases horizontalThreeDMTypedSourceComputed_arityTwoOrThree
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) clause member with two | three
  · simp [two]
  · simp [three]

/-- The retained clause-frame boundaries have exactly the actual normalized
source's clause lengths, in the same order. -/
theorem directSourceFinalClauseFrameBlockLengths_eq_horizontal
    (symbols : List encoding.Γ) :
    (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
        (directSourceFinalClauseDescriptors decider symbols)).map List.length =
      (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.map List.length := by
  rw [directSourceFinalClauseFrameBlockLengths_eq_fanArities,
    directSourceFinalClauseFanArities_eq_typedLengths]
  unfold horizontalThreeDMTypedSourceComputed
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]

/-- The numeric parent compiler broadcasts the actual normalized clause
positions over their own literal blocks. -/
theorem directSourceFinalOccurrenceParentIndices_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceParentIndices decider symbols =
      FiniteBlockIndices.expected List.length (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses := by
  rw [directSourceFinalOccurrenceParentIndices_eq_expected]
  exact FiniteBlockIndices.expected_eq_of_lengths List.length List.length _ _
    (directSourceFinalClauseFrameBlockLengths_eq_horizontal decider symbols)

/-- Regrouping preserves the exact parent clause of each actual occurrence
entry, rather than only its connector kind or fan fields. -/
theorem directSourceFinalGroupedParentIndices_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedParentIndices decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (fun entry => occurrenceClauseIndex (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2) := by
  rw [directSourceFinalGroupedParentIndices_eq_map_getD,
    directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries, List.map_map,
    directSourceFinalOccurrenceParentIndices_eq_horizontal]
  have arity := horizontalThreeDMTypedSourceComputed_arityTwoOrThree
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  unfold horizontalThreeDMTypedSourceComputed at arity
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData] at arity
  have nonempty : ∀ clause ∈ (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses, clause ≠ [] := by
    intro clause member empty
    have lengths := arity clause member
    simp [empty] at lengths
  apply List.map_congr_left
  intro entry member
  obtain ⟨tagged, lookup⟩ := occurrenceAt_exists_of_entry_mem
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry member
  have selected := clauseParentIndices_getD_of_occurrenceAt
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase nonempty
    entry.1 entry.2 tagged lookup
  simpa only [Function.comp_def, occurrenceClauseIndex, lookup] using selected

end LeanTrominoes.PeriodicCNFStripReduction

end
