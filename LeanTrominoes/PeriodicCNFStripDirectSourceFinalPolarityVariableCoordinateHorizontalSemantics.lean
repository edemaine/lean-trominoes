/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityVariableCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementBridge

/-! # Compiled variable coordinates agree with the complete horizontal source -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

private theorem eq_map_of_pointwise_lookup {Source Target : Type}
    (source : List Source) (values : List Target) (value : Source → Target)
    (lengths : values.length = source.length)
    (lookup : ∀ (index : Nat) (atom : Source), source[index]? = some atom → values[index]? = some (value atom)) :
    values = source.map value := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map]
  cases selected : source[index]? with
  | none =>
      simp only [Option.map_none]
      apply List.getElem?_eq_none_iff.mpr
      rw [lengths]
      exact List.getElem?_eq_none_iff.mp selected
  | some atom =>
      simp only [Option.map_some]
      exact lookup index atom selected

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance horizontalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- At each actual horizontal occurrence, the compiled coordinate names its
actual positioned variable, with all source conditions discharged. -/
theorem directSourceFinalPolarityVariableCoordinates_horizontal_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) (index : Nat)
    (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (atom : RoutedVariable)
    (atomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom) :
    (directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).position atom)) := by
  have indexLt := (List.getElem?_eq_some_iff.mp lookup).1
  have decoded := directSourceFinalOccurrence_atom_eq_of_horizontal_lookup decider symbols index indexLt atom atomLookup
  rw [(List.getElem?_eq_some_iff.mp lookup).2] at decoded
  have sourceLocal : (directSourceFormula decider symbols).IsLocal :=
    sourceFormula_isLocal (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3 :=
    sourceFormula_widthAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
      (directSourceFormula decider symbols) :=
    PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
  have sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [] :=
    sourceFormula_clausesNonempty (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have coordinate := directSourceFinalPolarityVariableCoordinates_lookup decider horizontal keepPositive symbols
    sourceLocal sourceWidth sourceOccurrences sourceNonempty index occurrence lookup witness atom
    (by simpa only [sourceOccurrencePolarityDescriptor, directSourceFinalGaugedFormula,
      directSourceFinalClockwiseFormula, directSourceFinalGaugedPlacement,
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula] using decoded)
  rw [horizontalRoutedPlacementComputed_eq_semantic]
  exact coordinate

/-- The entire emitted column is the actual horizontal formula's variable
positions in clause-major, literal-minor order. -/
theorem directSourceFinalPolarityVariableCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive symbols =
      (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
        (fun atom => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).position atom)) := by
  have lengths := congrArg List.length (directSourceFinalOccurrences_map_atom_eq_horizontal decider symbols)
  simp only [List.length_map] at lengths
  apply eq_map_of_pointwise_lookup
  · rw [directSourceFinalPolarityVariableCoordinates_length,
      ← lengths, directSourceFinalOccurrences_length_eq_compiled]
  · intro index atom atomLookup
    have indexLt : index < (directSourceFinalOccurrences decider symbols).length := by
      rw [lengths]
      exact (List.getElem?_eq_some_iff.mp atomLookup).1
    exact directSourceFinalPolarityVariableCoordinates_horizontal_lookup
      decider horizontal keepPositive symbols index (directSourceFinalOccurrences decider symbols)[index]
      (List.getElem?_eq_getElem indexLt) (directSourceFinalOccurrenceWitness decider symbols index indexLt)
      atom atomLookup

/-- Coordinate fields of every actual horizontal routed variable occurrence. -/
def directSourceFinalHorizontalVariableCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
    (fun atom => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
      ((horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).position atom))

/-- The native compiler emits the actual geometric variable-coordinate
column in polynomial time, with no residual source or agreement hypotheses. -/
noncomputable def directSourceFinalHorizontalVariableCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalHorizontalVariableCoordinates decider horizontal keepPositive) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalPolarityVariableCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalPolarityVariableCoordinates_eq_horizontal decider horizontal keepPositive symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
