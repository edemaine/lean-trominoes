/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSplitCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceAtomValueRows

/-! # Broadcast actual copied-literal coordinates into final occurrence rows -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing PeriodicEightOccurrenceSplit PeriodicThreeSATThree
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeaderPresentationAtomScope

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance copiedCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- The existing presentation-slot queries now read coordinate fields. -/
def directSourceFinalCopiedCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (directSourceFinalSplitCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalCopiedCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCopiedCoordinates HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime id
      (directSourceFinalCopiedSourcePositions decider)
      (directSourceFinalSplitCoordinates decider horizontal keepPositive)
      (directSourceFinalCopiedSourcePositionsComputableInPolyTime decider)
      (directSourceFinalSplitCoordinatesComputableInPolyTime decider horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

@[simp] theorem directSourceFinalCopiedCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCopiedCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedCoordinates HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
  rw [UnaryIndexedValueLookup.values_length]
  exact directSourceFinalCopiedSourcePositions_length decider symbols

/-- Actual parent coordinate rows, including the copied phase's first-literal
fallback at unused parent-local positions. -/
def directSourceFinalCopiedCoordinateValueBlocks (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × SourceOccurrenceAtomValueRow) :=
  let source := directSourceFormula decider symbols
  (finalCoordinatedSource source).clauses.zipIdx.map fun tagged =>
    let values := (copiedOccurrenceClause source tagged.2 tagged.1).literals.map fun literal =>
      CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position literal.atom)
    (copiedClauseProfile source tagged.2 tagged.1, { literals := values, localFallback := values.getD 0 0 })

private theorem copiedRow_value (values : List Nat) (control : HorizontalRoutedRouteHeader.AtomScopeControl) :
    ({ literals := values, localFallback := values.getD 0 0 } : SourceOccurrenceAtomValueRow).value control =
      values.getD (HorizontalRoutedRouteHeaderCopiedSourcePosition.scopeOffset control) 0 := by
  cases control <;> rfl

theorem directSourceFinalCopiedCoordinates_eq_value_blocks (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalCopiedCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCopiedCoordinateValueBlocks decider horizontal keepPositive symbols).flatMap
        (fun block => (clauseBlock block.1).map block.2.value) := by
  let source := directSourceFormula decider symbols
  let blocks := (finalCoordinatedSource source).clauses.zipIdx.map fun tagged =>
    (copiedClauseProfile source tagged.2 tagged.1,
      (copiedOccurrenceClause source tagged.2 tagged.1).literals.map fun literal =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position literal.atom))
  have tokensEq : blocks.map (fun block => Token.clause block.1) =
      directRetainedFigureNineCopiedClauseDescriptors decider symbols := by
    change _ = copiedClauseDescriptors source
    simp only [blocks, copiedClauseDescriptors, List.map_map, Function.comp_def]
  have valuesEq : blocks.flatMap Prod.snd =
      directSourceFinalSplitCoordinates decider horizontal keepPositive symbols := by
    rw [directSourceFinalSplitCoordinates_eq_copied_positions]
    simp only [blocks, copiedOccurrenceClauses, List.flatMap_map, source]
  have lengths : ∀ block ∈ blocks, block.2.length =
      HorizontalRoutedRouteHeaderCopiedSourcePosition.sourceWordCount block.1 := by
    intro block member
    obtain ⟨tagged, taggedMember, rfl⟩ := List.mem_map.mp member
    have clauseMember := List.fst_mem_of_mem_zipIdx taggedMember
    have literalMember : tagged.1.literals ∈
        PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses source := by
      rw [← finalCoordinatedSource_clauseLiterals_eq]
      exact List.mem_map.mpr ⟨tagged.1, clauseMember, rfl⟩
    have nonempty := directSource_deduplicatedClauses_nonempty decider symbols _ literalMember
    have width := directSource_deduplicatedClauses_widthAtMostThree decider symbols _ literalMember
    simp only [List.length_map, copiedOccurrenceClause, PeriodicEightOccurrenceSplit.occurrenceClause,
      List.length_zipIdx, HorizontalRoutedRouteHeaderCopiedSourcePosition.sourceWordCount,
      HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount, copiedClauseProfile]
    rw [DirectedClauseProfile.taggedLiterals_ofList _
      (by simpa using nonempty) (by simpa using width)]
    simp only [List.length_map, List.length_zipIdx]
  rw [directSourceFinalCopiedCoordinates, ← tokensEq, ← valuesEq,
    HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_clauseBlocks blocks lengths]
  simp only [blocks, directSourceFinalCopiedCoordinateValueBlocks, List.flatMap_map, source]
  apply List.flatMap_congr
  intro tagged _member
  apply List.map_congr_left
  intro control _controlMember
  exact (copiedRow_value _ control).symm

theorem directSourceFinalCopiedCoordinateValueBlocks_profiles (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCopiedCoordinateValueBlocks decider horizontal keepPositive symbols).map
        (fun block => Token.clause block.1) = directRetainedFigureNineCopiedClauseDescriptors decider symbols := by
  change _ = copiedClauseDescriptors (directSourceFormula decider symbols)
  simp only [directSourceFinalCopiedCoordinateValueBlocks, copiedClauseDescriptors, List.map_map, Function.comp_def]

theorem directSourceFinalCopiedCoordinateValueBlocks_literals (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCopiedCoordinateValueBlocks decider horizontal keepPositive symbols).map
        (fun block => block.2.literals) =
      (copiedOccurrenceClauses (directSourceFormula decider symbols)).map fun clause => clause.literals.map fun literal =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            (directSourceFormula decider symbols)).position literal.atom) := by
  simp only [directSourceFinalCopiedCoordinateValueBlocks, copiedOccurrenceClauses, List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicCNFStripReduction
end
