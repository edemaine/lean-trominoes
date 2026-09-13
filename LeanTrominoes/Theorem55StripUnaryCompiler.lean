/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryTables
import LeanTrominoes.UnaryKeyMembershipCompiler
import LeanTrominoes.Theorem55StripEncoding

/-! # A polynomial-time unary strip-to-complement compiler -/

noncomputable section
namespace LeanTrominoes.Theorem55StripUnary
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

def keep (source : PeriodicStrip) (point : Nat×Nat) : Bool :=
  !decide (key source (point.1+1,point.2+1) ∈ excludedKeys source)

def keepCompiler : TM2ComputableInPolyTime encode id
    (fun source => (gridTable.rows source).map (keep source)) := by
  let query := (gridTable.affine 1 1 1).keyCompiler radix radixCompiler
  let member := UnaryKeyMembership.computableInPolyTime encode _ excludedKeys query excludedKeyCompiler
  let negated := AlignedBooleanListClosure.mapNegatedComputableInPolyTime encode _ member
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq negated
    (fun source => by simp [keep,UnaryPointTable.affine,AlignedBooleanListClosure.negated,
      List.map_map,Function.comp_def,key])

def ordinaryTable : UnaryPointTable encode := gridTable.filter keep keepCompiler

def natCell (point : Nat×Nat) : Cell := (point.1,point.2)
def leftKeyCells : List Cell := [(-4,2),(-4,3),(-3,3),(-2,3),(-1,3)]
def leftKeyFields : List Nat := [7,4,7,6,5,6,3,6,1,6]

def compiledInput (source : PeriodicStrip) : Theorem55.StripInput :=
  (side source,(ordinaryTable.rows source).map natCell ++ leftKeyCells)

def ordinaryCountCompiler : Compiler (fun source => [(ordinaryTable.rows source).length+5]) := by
  let counted := TM2CompositionMachine.computableInPolyTime ordinaryTable.xCompiler UnaryFieldAggregate.countCompiler
  let shifted := offsetCompiler _ counted 5
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq shifted
    (fun s => congrArg unaryFields (by simp))

def outputFields (source : PeriodicStrip) : List Nat :=
  [side source,(ordinaryTable.rows source).length+5] ++
    (ordinaryTable.rows source).flatMap (fun p => [p.1*2,p.2*2]) ++ leftKeyFields

def outputFieldsCompiler : Compiler outputFields := by
  let header := UnaryFieldClosure.appendCompiler encode _ _ sideCompiler ordinaryCountCompiler
  let coordinates := (ordinaryTable.affine 2 0 0).fieldsCompiler
  let body := UnaryFieldClosure.appendCompiler encode _ _ coordinates (constantCompiler leftKeyFields)
  let compiler := UnaryFieldClosure.appendCompiler encode _ _ header body
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun s => congrArg unaryFields (by simp [outputFields,side,UnaryPointTable.affine,List.flatMap_map,List.append_assoc]))

theorem outputFields_correct (source : PeriodicStrip) :
    outputFields source = Theorem55StripEncoding.fields (compiledInput source) := by
  have left : leftKeyCells.flatMap PeriodicStripFlatEncoding.cellFields = leftKeyFields := by decide
  simp only [Theorem55StripEncoding.fields,compiledInput,List.length_append,List.length_map,
    List.flatMap_append,List.flatMap_map,left,show leftKeyCells.length = 5 from rfl]
  unfold outputFields
  rw [List.append_assoc]
  congr 2
  apply List.flatMap_congr
  intro p _
  change [p.1*2,p.2*2] = [2*p.1,2*p.2]
  simp [Nat.mul_comm]

def boolBlock : UnaryFieldEncoderMachine.Symbol → List Bool
  | .unit => [true]
  | .delimiter => [false]

theorem bool_field (n : Nat) : (UnaryFieldEncoderMachine.unaryField n).flatMap boolBlock =
    List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [UnaryFieldEncoderMachine.unaryField,List.replicate_succ,boolBlock] using congrArg (true :: ·) ih

theorem bool_fields (values : List Nat) : (unaryFields values).flatMap boolBlock =
    Theorem55StripEncoding.unaryFields values := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    rw [UnaryFieldEncoderMachine.unaryFields_cons,List.flatMap_append,bool_field,ih]
    rfl

def boolEncoder : TM2ComputableInPolyTime unaryFields Theorem55StripEncoding.unaryFields id := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime boolBlock) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw bool_fields

/-- Actual polynomial-time machine on the unary source fields; no size-only shortcut. -/
def compiler : TM2ComputableInPolyTime encode Theorem55StripEncoding.finEncoding.encode compiledInput := by
  let compiled := TM2CompositionMachine.computableInPolyTime outputFieldsCompiler boolEncoder
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun source => congrArg Theorem55StripEncoding.unaryFields (outputFields_correct source))

end LeanTrominoes.Theorem55StripUnary
