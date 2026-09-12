/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedAtomHorizontalSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedFinalGaugedInheritedPosition
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Actual inherited Figure 9 coordinates in coherent occurrence order -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeader PlanarOneInThreeNoUnitsFigureNine

private theorem pointValue_scale144 (field : CarrierCrossingPointField.Field) (point : Cell) :
    CarrierCrossingPointField.pointValue field (Cell.scale 144 point) =
      CarrierCrossingPointField.pointValue field point * 144 := by
  rcases point with ⟨x, y⟩
  cases field <;> simp only [CarrierCrossingPointField.pointValue, CarrierCrossingPointField.horizontal,
    CarrierCrossingPointField.keepPositive, Cell.scale, Bool.false_eq_true, ↓reduceIte] <;> omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance composedInheritedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- The inherited coordinate and actual template instantiation select the
same ring atom at the same complete occurrence index. -/
theorem directSourceFinalInheritedCoordinates_witness
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (occurrenceLookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot) :
    ∃ atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable),
      instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
        witness.metadata.sourceClause (prefixAtom occurrence.header.figurePrefix) = .inl (.inl atom) ∧
      (directSourceFinalInheritedCoordinates decider horizontal keepPositive symbols)[index]? =
        some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            (directSourceFormula decider symbols)).position atom)) ∧
      atom ∈ (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).erase.variableOccurrences := by
  have querySelected := selected
  rw [prefixAtom_eq_localQuery] at querySelected
  obtain ⟨literal, literalLookup, atomEq⟩ := witness.inheritedSourceLiteral slot querySelected
  have scope := sourceOccurrenceScope_of_inherited occurrence original slot selected
  have valueEq := sourceOccurrenceCopiedValue_eq_literal
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      (directSourceFormula decider symbols)).clauses
    (fun atom => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        (directSourceFormula decider symbols)).position atom))
    occurrence witness.refinedClause literal slot witness.sourceLookup scope literalLookup
  refine ⟨literal.atom, ?_, ?_, ?_⟩
  · simpa only [prefixAtom_eq_localQuery] using atomEq
  · rw [directSourceFinalInheritedCoordinates_eq_occurrence_rows, List.getElem?_map,
      occurrenceLookup, Option.map_some,
      sourceOccurrenceAtomValue_eq_copiedValue_of_inherited _ occurrence slot scope, List.map_map]
    simp only [Function.comp_def]
    rw [directSourceFinalCoordinateValueBlocks_literals, valueEq]
  · simp only [PeriodicCNF.variableOccurrences, PositionedPeriodicCNF.erase, List.flatMap_map]
    exact List.mem_flatMap.mpr ⟨witness.refinedClause,
      List.mem_iff_getElem?.mpr ⟨occurrence.parentClauseIndex, witness.sourceLookup⟩,
      List.mem_map.mpr ⟨literal, List.mem_iff_getElem?.mpr ⟨_, literalLookup⟩, rfl⟩⟩

/-- Apply all three physical refinements to inherited coordinate fields. -/
def directSourceFinalComposedInheritedCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 144 (directSourceFinalInheritedCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalComposedInheritedCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalComposedInheritedCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalComposedInheritedCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalInheritedCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (UnaryFieldConstantScale.computableInPolyTime 144)

@[simp] theorem directSourceFinalComposedInheritedCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalComposedInheritedCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalComposedInheritedCoordinates, UnaryFieldConstantScale.values, List.length_map,
    directSourceFinalInheritedCoordinates_length]

/-- Original inherited occurrences emit their exact final gauged variable
coordinates; the source membership also proves the gauge leaves them fixed. -/
theorem directSourceFinalComposedInheritedCoordinates_finalGauged_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot) :
    (directSourceFinalComposedInheritedCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols)).position
          (instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
            witness.metadata.sourceClause (prefixAtom occurrence.header.figurePrefix)))) := by
  obtain ⟨atom, atomEq, coordinateLookup, member⟩ := directSourceFinalInheritedCoordinates_witness
    decider horizontal keepPositive symbols index occurrence witness lookup original slot selected
  rw [directSourceFinalComposedInheritedCoordinates, UnaryFieldConstantScale.values, List.getElem?_map,
    coordinateLookup, Option.map_some, atomEq, retainedFinalGaugedInheritedPosition _ atom member, pointValue_scale144]

end LeanTrominoes.PeriodicCNFStripReduction
end
