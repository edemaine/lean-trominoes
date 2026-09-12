/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFanHorizontalCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalClauseGadgetOriginIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineClauseElementTableScan
import LeanTrominoes.SignedUnaryCoordinateIndexedTableExpansion

/-! # Native coordinates for every retained colored clause vertex -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing Gadget PeriodicCNF PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM

private theorem pointValue_function (horizontal positive : Bool) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) =
      (fun point => SignedUnaryCoordinateRefinement.field positive
        (DelimitedDirectionDisplacement.component horizontal point)) := by
  funext point
  cases horizontal <;> cases positive <;> rfl

private theorem component_add (horizontal : Bool) (origin offset : Cell) :
    DelimitedDirectionDisplacement.component horizontal (Cell.add origin offset) =
      DelimitedDirectionDisplacement.component horizontal origin +
        DelimitedDirectionDisplacement.component horizontal offset := by
  cases horizontal <;> rfl

/-- The compiled origin list uses precisely the typed clause indices of the
retained-element table scan. -/
theorem horizontalClauseGadgetOrigins_eq_typedIndexed (source : PeriodicCNF Nat) :
    horizontalClauseGadgetOrigins source =
      (horizontalThreeDMTypedSourceComputed source).clauses.zipIdx.map
        (fun tagged => horizontalThreeDMClauseOriginComputed source tagged.2) := by
  rw [horizontalClauseGadgetOrigins_eq_indexed]
  simp only [horizontalThreeDMTypedSourceComputed, PositionedPeriodicCNF.erase,
    List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq]

/-- The full retained-vertex position stream of one color, in canonical order. -/
def horizontalRetainedElementPositions (source : PeriodicCNF Nat) (color : WireColor) : List Cell :=
  (horizontalThreeDMTypedSourceComputed source).clauses.zipIdx.flatMap
    (horizontalThreeDMRetainedClausePositionBlockComputed source color)

private def retainedElementLocalTable (color : WireColor) (ternary : Bool) : List Cell :=
  horizontalThreeDMRetainedClauseLocalPositions color (if ternary then 3 else 2)

private theorem retainedElementLocalTable_length_pos (color : WireColor) (ternary : Bool) :
    0 < (retainedElementLocalTable color ternary).length := by
  cases ternary <;> simp [retainedElementLocalTable]

private theorem retainedElementLocalTable_eq (color : WireColor) (size : Nat) :
    retainedElementLocalTable color (decide (size = 3)) =
      horizontalThreeDMRetainedClauseLocalPositions color size := by
  by_cases ternary : size = 3 <;>
    simp [retainedElementLocalTable, horizontalThreeDMRetainedClauseLocalPositions, ternary]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- One finite arity bit per actual clause. -/
def directSourceFinalClauseTernaryBits (symbols : List encoding.Γ) : List Bool :=
  (directSourceFinalClauseFans decider symbols).map ClauseRibbonFanData.hasRight

noncomputable def directSourceFinalClauseTernaryBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalClauseTernaryBits decider) := by
  let projected := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFansComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime (fun fan : ClauseRibbonFanData => [fan.hasRight]))
  apply Turing.TM2ComputableInPolyTime.of_eq projected
  intro symbols
  unfold directSourceFinalClauseTernaryBits
  rw [← List.map_eq_flatMap]

theorem directSourceFinalClauseTernaryBits_eq_typedIndexed (symbols : List encoding.Γ) :
    directSourceFinalClauseTernaryBits decider symbols =
      (horizontalThreeDMTypedSourceComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.zipIdx.map
        (fun tagged => decide (tagged.1.length = 3)) := by
  unfold directSourceFinalClauseTernaryBits
  rw [directSourceFinalClauseFans_hasRight_eq_typedClauseTernary]
  simpa only [List.map_map, Function.comp_def] using
    (congrArg (List.map (fun clause => decide (clause.length = 3)))
      (List.zipIdx_map_fst 0
        (horizontalThreeDMTypedSourceComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses)).symm

/-- Select the three- or four-position local table at each compiled clause origin. -/
def directSourceFinalRetainedElementCoordinates (color : WireColor) (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateIndexedTableExpansion.values
    (fun ternary => (retainedElementLocalTable color ternary).map
      (DelimitedDirectionDisplacement.component horizontal)) keepPositive
    (directSourceFinalClauseTernaryBits decider symbols)
    (fun positive => directSourceFinalClauseGadgetOriginCoordinates decider horizontal positive symbols)

noncomputable def directSourceFinalRetainedElementCoordinatesComputableInPolyTime
    (color : WireColor) (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRetainedElementCoordinates decider color horizontal keepPositive) := by
  unfold directSourceFinalRetainedElementCoordinates
  exact SignedUnaryCoordinateIndexedTableExpansion.nativeListComputableInPolyTime _ keepPositive
    (directSourceFinalClauseTernaryBits decider)
    (fun positive => directSourceFinalClauseGadgetOriginCoordinates decider horizontal positive)
    (directSourceFinalClauseTernaryBitsComputableInPolyTime decider)
    (fun positive => directSourceFinalClauseGadgetOriginCoordinatesComputableInPolyTime decider horizontal positive)

/-- Every signed coordinate column agrees with the exact retained-clause table scan. -/
theorem directSourceFinalRetainedElementCoordinates_eq_horizontal
    (color : WireColor) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalRetainedElementCoordinates decider color horizontal keepPositive symbols =
      (horizontalRetainedElementPositions (PolySpaceCompiler.formulaOfSymbols decider symbols) color).map
        (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)) := by
  unfold directSourceFinalRetainedElementCoordinates
  simp only [directSourceFinalClauseTernaryBits_eq_typedIndexed,
    directSourceFinalClauseGadgetOriginCoordinates_eq_horizontal,
    horizontalClauseGadgetOrigins_eq_typedIndexed, List.map_map, Function.comp_def, pointValue_function]
  rw [SignedUnaryCoordinateIndexedTableExpansion.values_map _ _ _ _ _ (fun entry _ => by
    rw [List.length_map]
    exact retainedElementLocalTable_length_pos _ _)]
  simp only [horizontalRetainedElementPositions, horizontalThreeDMRetainedClausePositionBlockComputed,
    List.map_flatMap, List.map_map, Function.comp_def, retainedElementLocalTable_eq, component_add]

end LeanTrominoes.PeriodicCNFStripReduction
end
