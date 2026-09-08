/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFirstParentRouteCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairOccurrenceDataSemantics
import LeanTrominoes.FirstParentInheritedRouteSelection
import LeanTrominoes.UnaryFieldBooleanFilterNativeListCompiler

/-! # One compiled first-literal coordinate per actual parent clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeaderPresentationAtomScope

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance firstParentCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

def directSourceFinalFirstParentCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues (directSourceFinalFirstParentRouteControls decider symbols)
    (directSourceFinalInheritedCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalFirstParentCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFirstParentCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalFirstParentCoordinates
  exact UnaryFieldBooleanFilter.selectedValuesNativeListComputableInPolyTime
    (directSourceFinalFirstParentRouteControls decider)
    (directSourceFinalInheritedCoordinates decider horizontal keepPositive)
    (directSourceFinalFirstParentRouteControlsComputableInPolyTime decider)
    (directSourceFinalInheritedCoordinatesComputableInPolyTime decider horizontal keepPositive)

/-- The same selector used by route displacements takes the first literal
coordinate in each actual parent row. -/
theorem directSourceFinalFirstParentCoordinates_eq_value_blocks (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalFirstParentCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateValueBlocks decider horizontal keepPositive symbols).map
        (fun block => block.2.literals.getD 0 0) := by
  rw [directSourceFinalFirstParentCoordinates, directSourceFinalInheritedCoordinates_eq_value_blocks]
  unfold directSourceFinalFirstParentRouteControls
  rw [← directSourceFinalCoordinateValueBlocks_profiles decider horizontal keepPositive]
  simp only [FirstParentInheritedRoute.output, List.flatMap_map, FirstParentInheritedRoute.controlBlock]
  rw [UnaryFieldBooleanFilter.selectedValues_flatMap _ _ _ (by
    intro block _member
    simp only [FirstParentInheritedRoute.controls_length, List.length_map, clauseBlock])]
  simp only [FirstParentInheritedRoute.selectedValues_literalRow, ← List.map_eq_flatMap]

/-- Actual clause order and literal order determine the entire output column. -/
theorem directSourceFinalFirstParentCoordinates_eq_literals (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalFirstParentCoordinates decider horizontal keepPositive symbols =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.map fun clause =>
          (clause.literals.map fun literal => CarrierCrossingPointField.pointValue
            (coordinateFieldOfBools horizontal keepPositive)
            ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              (directSourceFormula decider symbols)).position literal.atom)).getD 0 0 := by
  rw [directSourceFinalFirstParentCoordinates_eq_value_blocks]
  have rows := congrArg (List.map (fun values : List Nat => values.getD 0 0))
    (directSourceFinalCoordinateValueBlocks_literals decider horizontal keepPositive symbols)
  simpa only [List.map_map, Function.comp_def] using rows

@[simp] theorem directSourceFinalFirstParentCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalFirstParentCoordinates decider horizontal keepPositive symbols).length =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.length := by
  rw [directSourceFinalFirstParentCoordinates_eq_literals, List.length_map]

/-- Coordinates and displacements contain one entry for the same parent list. -/
theorem directSourceFinalFirstParentRouteDisplacements_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalFirstParentRouteDisplacements decider horizontal keepPositive symbols).length =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.length := by
  rw [← directSourceFinalFirstParentCoordinates_length decider horizontal keepPositive symbols]
  unfold directSourceFinalFirstParentRouteDisplacements directSourceFinalFirstParentCoordinates
  apply UnaryFieldBooleanFilter.selectedValues_length_congr
  rw [directSourceFinalParentRouteDisplacementCandidates_length, directSourceFinalInheritedCoordinates_length,
    directSourceFinalCompiledOccurrenceData_eq_routePairs, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
