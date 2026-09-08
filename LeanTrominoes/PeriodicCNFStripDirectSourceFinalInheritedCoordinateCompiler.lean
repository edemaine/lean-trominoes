/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceBlocks
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Complete inherited coordinates in coherent final occurrence order -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeaderPresentationAtomScope

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance inheritedCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- The copied prefix and cycle suffix use the same order as final occurrences. -/
def directSourceFinalInheritedCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalCopiedCoordinates decider horizontal keepPositive symbols ++
    directSourceFinalCycleCoordinates decider horizontal keepPositive symbols

noncomputable def directSourceFinalInheritedCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalInheritedCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalInheritedCoordinates
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalCopiedCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (directSourceFinalCycleCoordinatesComputableInPolyTime decider horizontal keepPositive)

@[simp] theorem directSourceFinalInheritedCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalInheritedCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalInheritedCoordinates, List.length_append,
    directSourceFinalCopiedCoordinates_length, directSourceFinalCycleCoordinates_length,
    directSourceFinalCompiledOccurrenceData_eq_copied_cycle, List.length_append]

/-- Actual parent literal coordinate rows, with each phase's unused fallback. -/
def directSourceFinalCoordinateValueBlocks (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × SourceOccurrenceAtomValueRow) :=
  directSourceFinalCopiedCoordinateValueBlocks decider horizontal keepPositive symbols ++
    directSourceFinalCycleCoordinateValueBlocks decider horizontal keepPositive symbols

theorem directSourceFinalCycleCoordinateValueBlocks_profiles (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCycleCoordinateValueBlocks decider horizontal keepPositive symbols).map
        (fun block => Token.clause block.1) = directSourceFinalCycleClauseDescriptors decider symbols := by
  simpa only [directSourceFinalCycleAtomValueBlocks, directSourceFinalCycleCoordinateValueBlocks,
    directSourceFinalCycleCoordinateOwners, List.map_flatMap, List.map_map, Function.comp_def] using
    directSourceFinalCycleAtomValueBlocks_profiles decider symbols

theorem directSourceFinalCoordinateValueBlocks_profiles (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCoordinateValueBlocks decider horizontal keepPositive symbols).map
        (fun block => Token.clause block.1) = directSourceFinalClauseDescriptors decider symbols := by
  rw [directSourceFinalCoordinateValueBlocks, List.map_append, directSourceFinalCopiedCoordinateValueBlocks_profiles,
    directSourceFinalCycleCoordinateValueBlocks_profiles]
  rfl

theorem directSourceFinalCoordinateValueBlocks_literals (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCoordinateValueBlocks decider horizontal keepPositive symbols).map (fun block => block.2.literals) =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.map fun clause => clause.literals.map fun literal =>
          CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
            ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              (directSourceFormula decider symbols)).position literal.atom) := by
  rw [directSourceFinalCoordinateValueBlocks, List.map_append, directSourceFinalCopiedCoordinateValueBlocks_literals,
    directSourceFinalCycleCoordinateValueBlocks_literals, finalPositionedFormula_clauses_eq_descriptorBlocks, List.map_append]

theorem directSourceFinalInheritedCoordinates_eq_value_blocks (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalInheritedCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateValueBlocks decider horizontal keepPositive symbols).flatMap
        (fun block => (clauseBlock block.1).map block.2.value) := by
  rw [directSourceFinalInheritedCoordinates, directSourceFinalCopiedCoordinates_eq_value_blocks,
    directSourceFinalCycleCoordinates_eq_value_blocks, directSourceFinalCoordinateValueBlocks, List.flatMap_append]

/-- Every inherited coordinate is selected by its coherent occurrence's own
parent, profile, and presentation slot. -/
theorem directSourceFinalInheritedCoordinates_eq_occurrence_rows (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalInheritedCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalOccurrences decider symbols).map
        (sourceOccurrenceAtomValue ((directSourceFinalCoordinateValueBlocks decider horizontal keepPositive symbols).map Prod.snd)) := by
  rw [directSourceFinalInheritedCoordinates_eq_value_blocks,
    ← sourceOccurrences_map_atomValueRows (directSourceFinalCoordinateValueBlocks decider horizontal keepPositive symbols)
      (tailTables (directSourceFormula decider symbols))]
  unfold directSourceFinalOccurrences occurrences
  rw [directSourceFinalClauseDescriptors_eq_source_prefix, sourceOccurrences_append_variables,
    ← directSourceFinalCoordinateValueBlocks_profiles decider horizontal keepPositive]

end LeanTrominoes.PeriodicCNFStripReduction
end
