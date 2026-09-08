/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGlobalTerminalSlotCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.RetainedAngularFanSplitCoordinateFormula
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # Source-scaled ring coordinates from direct source symbols -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicThreeSATThree PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSplitCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- The exact pre-split source occurrence presentation. -/
def directSourceFinalCoordinateOccurrences (symbols : List encoding.Γ) :=
  allOccurrenceVariables (retainedFinalCoordinatedScaledSource
    (directSourceFormula decider symbols)).erase

private theorem occurrence_fst {Variable : Type} (source : PeriodicCNF Variable) :
    (allOccurrenceVariables source).map Prod.fst = source.variableOccurrences := by
  simp only [allOccurrenceVariables, PeriodicCNF.variableOccurrences, taggedLiterals,
    List.map_map, List.map_flatMap, Function.comp_def]
  have literalMap : ∀ clause : PeriodicClause Variable,
      clause.zipIdx.map (fun entry => entry.1.atom) = clause.map PeriodicLiteral.atom := by
    intro clause
    exact List.map_zipIdx_eq_map_of_mem clause (fun entry => entry.1.atom)
      PeriodicLiteral.atom (fun _ _ => rfl)
  simp_rw [literalMap]
  have clauses := List.zipIdx_map_fst 0 source.clauses
  conv_rhs => rw [← clauses, List.flatMap_map]

theorem directSourceFinalCoordinateOccurrences_map_fst (symbols : List encoding.Γ) :
    (directSourceFinalCoordinateOccurrences decider symbols).map Prod.fst =
      directSourceFinalCoordinateAtoms decider symbols := by
  rw [directSourceFinalCoordinateAtoms_eq_variableOccurrences]
  exact occurrence_fst _

def directSourceFinalCoordinateOccurrenceSlot (symbols : List encoding.Γ)
    (copy : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable)) : RetainedTerminalSlot :=
  boundedRetainedTerminalSlot (retainedOccurrenceGlobalStableTerminalRank
    (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
    (retainedFinalCoordinatedScaledSourceRoutes (directSourceFormula decider symbols)) copy)

/-- Ring copies selected by the compiled global angular ranks. -/
def directSourceFinalSplitCoordinateCopies (symbols : List encoding.Γ) :
    List (ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable)) :=
  (directSourceFinalCoordinateOccurrences decider symbols).map fun copy =>
    PeriodicEightOccurrenceSplit.copy copy.1
      (angularPortOfIndex (directSourceFinalCoordinateOccurrenceSlot decider symbols copy).val)

def directSourceFinalSplitLocalCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values
    (fun slot : RetainedTerminalSlot => CarrierCrossingPointField.pointValue
      (coordinateFieldOfBools horizontal keepPositive) (retainedSplitRingOffset (portIndex (angularPortOfIndex slot.val))))
    (BoundedRetainedTerminalSlots.slots (retainedOccurrenceGlobalStableTerminalRanks
      (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
      (retainedFinalCoordinatedScaledSourceRoutes (directSourceFormula decider symbols))))

noncomputable def directSourceFinalSplitLocalCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalSplitLocalCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalSplitLocalCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGlobalTerminalSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      (fun slot : RetainedTerminalSlot => CarrierCrossingPointField.pointValue
        (coordinateFieldOfBools horizontal keepPositive)
        (retainedSplitRingOffset (portIndex (angularPortOfIndex slot.val)))))

theorem directSourceFinalSplitLocalCoordinates_eq_occurrences
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalSplitLocalCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateOccurrences decider symbols).map fun copy =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          (retainedSplitRingOffset (portIndex (angularPortOfIndex
            (directSourceFinalCoordinateOccurrenceSlot decider symbols copy).val))) := by
  unfold directSourceFinalSplitLocalCoordinates FiniteUnaryFieldMap.values
    BoundedRetainedTerminalSlots.slots
  rw [retainedOccurrenceGlobalStableTerminalRanks_eq_map]
  simp only [List.map_map]
  rfl

theorem directSourceFinalSplitLocalCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalSplitLocalCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalSplitLocalCoordinates_eq_occurrences, List.length_map,
    ← directSourceFinalCoordinateOccurrences_map_fst decider symbols, List.length_map]

/-- All four signed coordinates after the source-clearance and fixed-eight
refinements, in the original occurrence order. -/
def directSourceFinalSplitCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 1152 keepPositive
    (fun positive => directSourceFinalCanonicalCoordinates decider
      (coordinateFieldOfBools horizontal positive) symbols)
    (fun positive => directSourceFinalSplitLocalCoordinates decider horizontal positive symbols)

noncomputable def directSourceFinalSplitCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalSplitCoordinates decider horizontal keepPositive) :=
  SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 1152 keepPositive
    (fun positive => directSourceFinalCanonicalCoordinates decider
      (coordinateFieldOfBools horizontal positive))
    (directSourceFinalSplitLocalCoordinates decider horizontal)
    (fun positive symbols => by rw [directSourceFinalCanonicalCoordinates_length,
      directSourceFinalCanonicalCoordinates_length])
    (fun positive symbols => by rw [directSourceFinalSplitLocalCoordinates_length,
      directSourceFinalCanonicalCoordinates_length])
    (fun positive => directSourceFinalCanonicalCoordinatesComputableInPolyTime decider
      (coordinateFieldOfBools horizontal positive))
    (directSourceFinalSplitLocalCoordinatesComputableInPolyTime decider horizontal)

private theorem pointValue_bools (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (if horizontal then point.1 else point.2) := by
  simp only [CarrierCrossingPointField.pointValue, coordinateFieldOfBools_horizontal,
    coordinateFieldOfBools_keepPositive, SignedUnaryCoordinateRefinement.field]

private theorem split_pointValue_bools {Atom : Type} [DecidableEq Atom]
    (source : PeriodicCNF Atom) (horizontal positive : Bool)
    (copy : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Atom)) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive)
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position copy) =
      SignedUnaryCoordinateRefinement.field positive
        (1152 * (let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).position copy.1
          if horizontal then position.1 else position.2) +
        (let offset := retainedSplitRingOffset copy.2.1
          if horizontal then offset.1 else offset.2)) := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_eq, pointValue_bools]
  cases horizontal <;> rfl

private theorem split_pointValue_copy {Atom : Type} [DecidableEq Atom]
    (source : PeriodicCNF Atom) (horizontal positive : Bool)
    (atom : WrappedPeriodicPlanarSATVariable Atom) (port : OccurrenceSplitRing.Port) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive)
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position
          (PeriodicEightOccurrenceSplit.copy atom port)) =
      SignedUnaryCoordinateRefinement.field positive
        (1152 * (let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).position atom
          if horizontal then position.1 else position.2) +
        (let offset := retainedSplitRingOffset (portIndex port)
          if horizontal then offset.1 else offset.2)) := by
  exact split_pointValue_bools source horizontal positive (PeriodicEightOccurrenceSplit.copy atom port)

theorem directSourceFinalSplitCoordinates_eq_positions (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) :
    directSourceFinalSplitCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalSplitCoordinateCopies decider symbols).map fun copy =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            (directSourceFormula decider symbols)).position copy) := by
  have original : ∀ positive,
      directSourceFinalCanonicalCoordinates decider (coordinateFieldOfBools horizontal positive) symbols =
        (directSourceFinalCoordinateOccurrences decider symbols).map fun copy =>
          SignedUnaryCoordinateRefinement.field positive
            (let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              (directSourceFormula decider symbols)).position copy.1
             if horizontal then position.1 else position.2) := by
    intro positive
    rw [directSourceFinalCanonicalCoordinates_eq_positions,
      ← directSourceFinalCoordinateOccurrences_map_fst decider symbols, List.map_map]
    apply List.map_congr_left
    intro copy _member
    exact pointValue_bools horizontal positive
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        (directSourceFormula decider symbols)).position copy.1)
  have localCoordinates : ∀ positive,
      directSourceFinalSplitLocalCoordinates decider horizontal positive symbols =
        (directSourceFinalCoordinateOccurrences decider symbols).map fun copy =>
          SignedUnaryCoordinateRefinement.field positive
            (let offset := retainedSplitRingOffset (portIndex (angularPortOfIndex
              (directSourceFinalCoordinateOccurrenceSlot decider symbols copy).val))
             if horizontal then offset.1 else offset.2) := by
    intro positive
    rw [directSourceFinalSplitLocalCoordinates_eq_occurrences]
    apply List.map_congr_left
    intro copy _member
    exact pointValue_bools horizontal positive
      (retainedSplitRingOffset (portIndex (angularPortOfIndex
        (directSourceFinalCoordinateOccurrenceSlot decider symbols copy).val)))
  unfold directSourceFinalSplitCoordinates
  rw [show (fun positive => directSourceFinalCanonicalCoordinates decider
      (coordinateFieldOfBools horizontal positive) symbols) = _ from funext original]
  rw [show (fun positive => directSourceFinalSplitLocalCoordinates decider horizontal positive symbols) = _
    from funext localCoordinates]
  rw [SignedUnaryCoordinateRefinement.values_map]
  unfold directSourceFinalSplitCoordinateCopies
  rw [List.map_map]
  apply List.map_congr_left
  intro copy _member
  exact (split_pointValue_copy (directSourceFormula decider symbols) horizontal keepPositive copy.1
    (angularPortOfIndex (directSourceFinalCoordinateOccurrenceSlot decider symbols copy).val)).symm

theorem directSourceFinalSplitCoordinates_length (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) :
    (directSourceFinalSplitCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalSplitCoordinates_eq_positions, List.length_map,
    directSourceFinalSplitCoordinateCopies, List.length_map,
    ← directSourceFinalCoordinateOccurrences_map_fst decider symbols, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
