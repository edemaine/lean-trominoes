/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryAlignedAddNativeListCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldUnitLengthBroadcastCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldConstantScaleCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.Computation.TM2.TM2NativeListAppendClosure

/-! # Actual polynomial-time coordinate columns for finite padding -/
noncomputable section
namespace LeanTrominoes.FiniteSparsePaddingColumns
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

def coordinates (column : List Nat) (units : List Unit) : List Nat :=
  UnaryAlignedAddMachine.sums column (UnaryFieldUnitLengthBroadcast.values column units)

theorem coordinates_eq_map (column : List Nat) (units : List Unit) :
    coordinates column units=column.map (fun value => value+units.length) := by
  unfold coordinates
  rw [UnaryFieldUnitLengthBroadcast.values_eq_map]
  simpa using UnaryAlignedAddMachine.sums_map column id (fun _ => units.length)

def complements (column : List Nat) (units : List Unit) : List Nat :=
  UnaryAlignedAddMachine.sums column
    (UnaryFieldConstantOffsets.values 2
      (UnaryFieldConstantScale.values 3 (UnaryFieldUnitLengthBroadcast.values column units)))

theorem complements_eq_map (column : List Nat) (units : List Unit) :
    complements column units=column.map (fun value => value+3*units.length+2) := by
  unfold complements
  rw [UnaryFieldUnitLengthBroadcast.values_eq_map]
  simp only [UnaryFieldConstantOffsets.values,UnaryFieldConstantScale.values,List.map_map,Function.comp_def]
  have eq := UnaryAlignedAddMachine.sums_map column id (fun _ => 3*units.length+2)
  simpa only [List.map_id,Nat.add_assoc,Nat.mul_comm,id_eq] using eq

def gridUnits (units : List Unit) : List Unit :=
  units.flatMap (fun _ => [(),(),()])++[()]

@[simp] theorem gridUnits_length (units : List Unit) :
    (gridUnits units).length=3*units.length+1 := by
  induction units with
  | nil => rfl
  | cons marker units ih =>
      simp only [gridUnits,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *
      omega

variable {Symbol : Type} [Fintype Symbol]
variable (column : List Symbol → List Nat) (units : List Symbol → List Unit)
variable (columnCompiler : TM2ComputableInPolyTime id unaryFields column)
variable (unitCompiler : TM2ComputableInPolyTime id id units)

def coordinatesComputableInPolyTime : TM2ComputableInPolyTime id unaryFields
    (fun source => coordinates (column source) (units source)) := by
  exact UnaryAlignedAddMachine.nativeListComputableInPolyTime column _
    (fun _ => (UnaryFieldUnitLengthBroadcast.values_length _ _).symm)
    columnCompiler (UnaryFieldUnitLengthBroadcast.nativeListComputableInPolyTime column units columnCompiler unitCompiler)

def complementsComputableInPolyTime : TM2ComputableInPolyTime id unaryFields
    (fun source => complements (column source) (units source)) := by
  let broadcast := UnaryFieldUnitLengthBroadcast.nativeListComputableInPolyTime column units columnCompiler unitCompiler
  let scaled := TM2CompositionMachine.computableInPolyTime broadcast (UnaryFieldConstantScale.computableInPolyTime 3)
  let offset := TM2CompositionMachine.computableInPolyTime scaled (UnaryFieldConstantOffsets.computableInPolyTime 2)
  exact UnaryAlignedAddMachine.nativeListComputableInPolyTime column _
    (fun source => by simp only [UnaryFieldConstantOffsets.values,UnaryFieldConstantScale.values,
      List.length_map,UnaryFieldUnitLengthBroadcast.values_length]) columnCompiler offset

def gridUnitsComputableInPolyTime : TM2ComputableInPolyTime id id
    (fun source => gridUnits (units source)) := by
  let triple := TM2CompositionMachine.computableInPolyTime unitCompiler
    (FiniteBlockTransducer.computableInPolyTime (fun _ : Unit => [(),(),()]))
  let endUnit : TM2ComputableInPolyTime (id : List Symbol → List Symbol) id (fun _ => [()]) :=
    TM2ConstantValueCompiler.computableInPolyTime id id [()]
  exact TM2ListAppend.nativeComputableInPolyTime triple endUnit
end LeanTrominoes.FiniteSparsePaddingColumns
