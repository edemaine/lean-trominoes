/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleCoordinateDataCompiler

/-! # Complete split-ring coordinates for final cycle occurrence rows -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance cycleCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- The ring variable selected at each final cycle row. Parent-local rows use
the same harmless default slot as the existing inherited-code compiler. -/
def directSourceFinalCycleCoordinateCopies (symbols : List encoding.Γ) :=
  (directSourceFinalCycleCoordinateEntries decider symbols).map fun entry =>
    ringCopy entry.1 (directFinalCycleRingVertexOfSlot entry.2)

def directSourceFinalCycleCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 1152 keepPositive
    (fun positive => directSourceFinalCycleOwnerCoordinates decider
      (coordinateFieldOfBools horizontal positive) symbols)
    (fun positive => directSourceFinalCycleLocalCoordinates decider
      (coordinateFieldOfBools horizontal positive) symbols)

noncomputable def directSourceFinalCycleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCycleCoordinates decider horizontal keepPositive) :=
  SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 1152 keepPositive
    (fun positive => directSourceFinalCycleOwnerCoordinates decider (coordinateFieldOfBools horizontal positive))
    (fun positive => directSourceFinalCycleLocalCoordinates decider (coordinateFieldOfBools horizontal positive))
    (fun positive symbols => by rw [directSourceFinalCycleOwnerCoordinates_length,
      directSourceFinalCycleOwnerCoordinates_length])
    (fun positive symbols => by rw [directSourceFinalCycleLocalCoordinates_length,
      directSourceFinalCycleOwnerCoordinates_length])
    (fun positive => directSourceFinalCycleOwnerCoordinatesComputableInPolyTime decider
      (coordinateFieldOfBools horizontal positive))
    (fun positive => directSourceFinalCycleLocalCoordinatesComputableInPolyTime decider
      (coordinateFieldOfBools horizontal positive))

private theorem pointValue_bools (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (if horizontal then point.1 else point.2) := by
  cases horizontal <;> cases positive <;> rfl

/-- Coordinates of the selected inherited ring copies in final cycle row order.
Parent-local rows carry the unused default vertex of the inherited-code stream. -/
theorem directSourceFinalCycleCoordinates_eq_positions (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) :
    directSourceFinalCycleCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCycleCoordinateCopies decider symbols).map fun copy =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            (directSourceFormula decider symbols)).position copy) := by
  have origins : ∀ positive,
      directSourceFinalCycleOwnerCoordinates decider (coordinateFieldOfBools horizontal positive) symbols =
        (directSourceFinalCycleCoordinateEntries decider symbols).map fun entry =>
          SignedUnaryCoordinateRefinement.field positive
            (let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              (directSourceFormula decider symbols)).position entry.1
             if horizontal then position.1 else position.2) := by
    intro positive
    rw [directSourceFinalCycleOwnerCoordinates_eq_entries]
    apply List.map_congr_left
    intro entry _member
    exact pointValue_bools horizontal positive
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        (directSourceFormula decider symbols)).position entry.1)
  have offsets : ∀ positive,
      directSourceFinalCycleLocalCoordinates decider (coordinateFieldOfBools horizontal positive) symbols =
        (directSourceFinalCycleCoordinateEntries decider symbols).map fun entry =>
          SignedUnaryCoordinateRefinement.field positive
            (let offset := retainedSplitRingVertexOffset (directFinalCycleRingVertexOfSlot entry.2)
             if horizontal then offset.1 else offset.2) := by
    intro positive
    rw [directSourceFinalCycleLocalCoordinates_eq_entries]
    apply List.map_congr_left
    intro entry _member
    exact pointValue_bools horizontal positive
      (retainedSplitRingVertexOffset (directFinalCycleRingVertexOfSlot entry.2))
  unfold directSourceFinalCycleCoordinates
  rw [show (fun positive => directSourceFinalCycleOwnerCoordinates decider
      (coordinateFieldOfBools horizontal positive) symbols) = _ from funext origins]
  rw [show (fun positive => directSourceFinalCycleLocalCoordinates decider
      (coordinateFieldOfBools horizontal positive) symbols) = _ from funext offsets]
  rw [SignedUnaryCoordinateRefinement.values_map]
  unfold directSourceFinalCycleCoordinateCopies
  rw [List.map_map]
  apply List.map_congr_left
  intro entry _member
  dsimp only [Function.comp_def]
  exact (retainedSplitRingCopy_coordinate (directSourceFormula decider symbols) horizontal keepPositive
    entry.1 (directFinalCycleRingVertexOfSlot entry.2)).symm

theorem directSourceFinalCycleCoordinates_length (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) :
    (directSourceFinalCycleCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCycleOccurrenceData decider symbols).length := by
  rw [directSourceFinalCycleCoordinates_eq_positions, List.length_map,
    directSourceFinalCycleCoordinateCopies, List.length_map]
  have lengthEq := congrArg List.length
    (directSourceFinalCycleOwnerCoordinates_eq_entries decider .horizontalPositive symbols)
  rw [directSourceFinalCycleOwnerCoordinates_length, List.length_map] at lengthEq
  exact lengthEq.symm

end LeanTrominoes.PeriodicCNFStripReduction
end
