/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalComposedVariableCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolaritySubdivisionCoordinateCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFreshPositions

/-! # Complete variable-coordinate compiler through polarity normalization -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open HorizontalRoutedRouteHeader PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Both uses of a newly inserted variable choose the first route point. -/
def headerIsPolarityFresh (header : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header) : Bool :=
  match header.polarity.operation with
  | .incompatible | .complementFresh => true
  | .compatible | .complementOriginal => false

local instance polarityFreshDecidable (occurrence : SourceOccurrence) : Decidable (sourceOccurrenceIsFresh occurrence) := by
  unfold sourceOccurrenceIsFresh
  infer_instance

theorem headerIsPolarityFresh_eq_decide (occurrence : SourceOccurrence) :
    headerIsPolarityFresh occurrence.header = decide (sourceOccurrenceIsFresh occurrence) := by
  cases operation : occurrence.header.polarity.operation <;> simp [headerIsPolarityFresh, sourceOccurrenceIsFresh, operation]

private theorem pointValue_scale3 (field : CarrierCrossingPointField.Field) (point : Cell) :
    CarrierCrossingPointField.pointValue field (Cell.scale 3 point) =
      CarrierCrossingPointField.pointValue field point * 3 := by
  rcases point with ⟨x, y⟩
  cases field <;> simp only [CarrierCrossingPointField.pointValue, CarrierCrossingPointField.horizontal,
    CarrierCrossingPointField.keepPositive, Cell.scale, Bool.false_eq_true, ↓reduceIte] <;> omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance polarityVariableStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

def directSourceFinalPolarityFreshBits (symbols : List encoding.Γ) : List Bool :=
  (sourceHeaders (directSourceFinalClauseDescriptors decider symbols)).flatMap fun header => [headerIsPolarityFresh header]

noncomputable def directSourceFinalPolarityFreshBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalPolarityFreshBits decider) := by
  let mapped := TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
      sourceHeadersComputableInPolyTime)
    (FiniteBlockTransducer.computableInPolyTime fun header => [headerIsPolarityFresh header])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq mapped (fun _ => rfl)

theorem directSourceFinalPolarityFreshBits_eq_occurrences (symbols : List encoding.Γ) :
    directSourceFinalPolarityFreshBits decider symbols =
      (directSourceFinalOccurrences decider symbols).map fun occurrence => headerIsPolarityFresh occurrence.header := by
  unfold directSourceFinalPolarityFreshBits
  rw [← List.map_eq_flatMap, directSourceFinalHeaders_eq_occurrences, List.map_map]
  rfl

@[simp] theorem directSourceFinalPolarityFreshBits_length (symbols : List encoding.Γ) :
    (directSourceFinalPolarityFreshBits decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalPolarityFreshBits_eq_occurrences, List.length_map, directSourceFinalOccurrences_length_eq_compiled]

/-- Original variables retain threefold-scaled Figure 9 coordinates. -/
def directSourceFinalPolarityOriginalCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 3 (directSourceFinalComposedVariableCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalPolarityOriginalCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalPolarityOriginalCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalPolarityOriginalCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalComposedVariableCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (UnaryFieldConstantScale.computableInPolyTime 3)

@[simp] theorem directSourceFinalPolarityOriginalCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalPolarityOriginalCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalPolarityOriginalCoordinates, UnaryFieldConstantScale.values, List.length_map,
    directSourceFinalComposedVariableCoordinates_length]

/-- Every final variable occurrence chooses either its scaled original
position or its first subdivision point. -/
def directSourceFinalPolarityVariableCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryBooleanChoice.selectedValues (directSourceFinalPolarityFreshBits decider symbols)
    (directSourceFinalPolarityOriginalCoordinates decider horizontal keepPositive symbols)
    (directSourceFinalPolaritySubdivisionCoordinates decider 1 horizontal keepPositive symbols)

noncomputable def directSourceFinalPolarityVariableCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalPolarityVariableCoordinates
    exact AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime id
      (directSourceFinalPolarityFreshBits decider)
      (directSourceFinalPolarityOriginalCoordinates decider horizontal keepPositive)
      (directSourceFinalPolaritySubdivisionCoordinates decider 1 horizontal keepPositive)
      (fun symbols => by rw [directSourceFinalPolarityFreshBits_length, directSourceFinalPolarityOriginalCoordinates_length])
      (fun symbols => by rw [directSourceFinalPolarityOriginalCoordinates_length, directSourceFinalPolaritySubdivisionCoordinates_length])
      (directSourceFinalPolarityFreshBitsComputableInPolyTime decider)
      (directSourceFinalPolarityOriginalCoordinatesComputableInPolyTime decider horizontal keepPositive)
      (directSourceFinalPolaritySubdivisionCoordinatesComputableInPolyTime decider 1 horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

@[simp] theorem directSourceFinalPolarityVariableCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalPolarityVariableCoordinates
  rw [AlignedUnaryBooleanChoice.selectedValues_length _ _ _
    (by rw [directSourceFinalPolarityFreshBits_length, directSourceFinalPolarityOriginalCoordinates_length]),
    directSourceFinalPolarityFreshBits_length]

/-- Every successful actual atom decoder gets its own exact routed polarity
position, covering all four operations and both occurrences of a fresh atom. -/
theorem directSourceFinalPolarityVariableCoordinates_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (sourceLocal : (directSourceFormula decider symbols).IsLocal)
    (sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3)
    (sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
      (directSourceFormula decider symbols))
    (sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [])
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (atom : RoutedVariable)
    (decoded : (sourceIndexedDescriptorOf occurrence.generatedClauseIndex occurrence.header.polarity.indexed).atom?
      (refinedSource
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols))).erase = some atom) :
    (directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((placement (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols))
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
            (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty)).position atom)) := by
  have compiledLt : index < (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← directSourceFinalOccurrences_length_eq_compiled]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have outputLt : index < (directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive symbols).length := by
    rw [directSourceFinalPolarityVariableCoordinates_length]
    exact compiledLt
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨outputLt, ?_⟩
  rw [← List.getD_eq_getElem _ 0 outputLt, directSourceFinalPolarityVariableCoordinates,
    AlignedUnaryBooleanChoice.selectedValues_getD _ _ _
      (by rw [directSourceFinalPolarityFreshBits_length, directSourceFinalPolarityOriginalCoordinates_length])
      (by rw [directSourceFinalPolarityOriginalCoordinates_length, directSourceFinalPolaritySubdivisionCoordinates_length])
      index (by rw [directSourceFinalPolarityFreshBits_length]; exact compiledLt)]
  have control : (directSourceFinalPolarityFreshBits decider symbols).getD index false =
      decide (sourceOccurrenceIsFresh occurrence) := by
    rw [directSourceFinalPolarityFreshBits_eq_occurrences, List.getD_eq_getElem?_getD,
      List.getElem?_map, lookup, Option.map_some, Option.getD_some, headerIsPolarityFresh_eq_decide]
  rw [control]
  by_cases fresh : sourceOccurrenceIsFresh occurrence
  · simp only [fresh, decide_true, ↓reduceIte]
    rw [witness.freshPolarityPosition sourceLocal sourceWidth sourceOccurrences sourceNonempty fresh atom decoded]
    have coordinates := directSourceFinalPolaritySubdivisionCoordinates_lookup
      decider 1 horizontal keepPositive symbols index occurrence lookup witness
    simpa only [List.getD_eq_getElem?_getD, Option.getD_some, polaritySubdivisionOffset,
      Nat.cast_one, Cell.scale, one_mul, Prod.eta] using congrArg (fun value => value.getD 0) coordinates
  · simp only [fresh, decide_false, Bool.false_eq_true, ↓reduceIte]
    have original : occurrence.header.polarity.operation = .compatible ∨
        occurrence.header.polarity.operation = .complementOriginal := by
      cases operation : occurrence.header.polarity.operation <;> simp_all [sourceOccurrenceIsFresh]
    have atomEq := witness.originalPolarityAtom sourceLocal sourceWidth sourceOccurrences sourceNonempty original atom decoded
    rw [atomEq, placement_original_position]
    change _ = CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
      (Cell.scale 3 ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        (directSourceFormula decider symbols)).position _))
    rw [pointValue_scale3]
    have coordinates := directSourceFinalComposedVariableCoordinates_finalGauged_lookup
      decider horizontal keepPositive symbols sourceLocal sourceWidth sourceOccurrences sourceNonempty
      index occurrence lookup witness fresh
    simp only [directSourceFinalPolarityOriginalCoordinates, UnaryFieldConstantScale.values,
      List.getD_eq_getElem?_getD, List.getElem?_map, coordinates, Option.map_some, Option.getD_some,
      prefixAtom_eq_localQuery]

end LeanTrominoes.PeriodicCNFStripReduction
end
