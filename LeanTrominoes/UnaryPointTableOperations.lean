/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryPointTableCompiler
import LeanTrominoes.UnaryAlignedWordPairCompiler

/-! # Filtering and serializing unary coordinate tables -/

noncomputable section
namespace LeanTrominoes.UnaryPointTable
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable {encode : Source → List Symbol}

def line (values : Source → List Nat)
    (compiler : TM2ComputableInPolyTime encode unaryFields values) (horizontal : Bool) : UnaryPointTable encode where
  rows s := (values s).map (fun n => if horizontal then (n,0) else (0,n))
  xCompiler := by
    cases horizontal
    · let zeros := TM2CompositionMachine.computableInPolyTime compiler UnaryFieldConstantStreams.zerosComputableInPolyTime
      exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq zeros
        (fun s => congrArg unaryFields (by simp [UnaryFieldConstantStreams.zeros,List.map_map,Function.comp_def]))
    · exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
        (fun s => congrArg unaryFields (by simp [List.map_map,Function.comp_def]))
  yCompiler := by
    cases horizontal
    · exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
        (fun s => congrArg unaryFields (by simp [List.map_map,Function.comp_def]))
    · let zeros := TM2CompositionMachine.computableInPolyTime compiler UnaryFieldConstantStreams.zerosComputableInPolyTime
      exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq zeros
        (fun s => congrArg unaryFields (by simp [UnaryFieldConstantStreams.zeros,List.map_map,Function.comp_def]))

def filter (a : UnaryPointTable encode) (test : Source → Nat×Nat → Bool)
    (compiler : TM2ComputableInPolyTime encode id (fun s => (a.rows s).map (test s))) : UnaryPointTable encode where
  rows s := (a.rows s).filter (test s)
  xCompiler := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime encode _ _ compiler a.xCompiler)
    (fun s => congrArg unaryFields (UnaryFieldCartesian.selected_map _ _ _))
  yCompiler := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime encode _ _ compiler a.yCompiler)
    (fun s => congrArg unaryFields (UnaryFieldCartesian.selected_map _ _ _))

private theorem interleaved_maps (rows : List (Nat×Nat)) :
    AlignedUnaryBooleanChoice.interleaved (rows.map Prod.fst) (rows.map Prod.snd) =
      rows.flatMap (fun p => [p.1,p.2]) := by
  induction rows with
  | nil => rfl
  | cons p rows ih => simpa [AlignedUnaryBooleanChoice.interleaved] using congrArg (p.1 :: p.2 :: ·) ih

def fieldsCompiler (a : UnaryPointTable encode) : TM2ComputableInPolyTime encode unaryFields
    (fun s => (a.rows s).flatMap (fun p => [p.1,p.2])) := by
  let left := TM2CompositionMachine.computableInPolyTime a.xCompiler
    UnaryFieldAlternatingPadding.appendZeroValuesComputableInPolyTime
  let right := TM2CompositionMachine.computableInPolyTime a.yCompiler
    UnaryFieldAlternatingPadding.prependZeroValuesComputableInPolyTime
  let merged := AlignedUnaryListClosure.addedComputableInPolyTime encode _ _ (fun s => by simp) left right
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq merged
  intro s
  congr 1
  change AlignedUnaryBooleanChoice.candidateValues _ _ = _
  rw [AlignedUnaryBooleanChoice.candidateValues_eq_interleaved,interleaved_maps]

end LeanTrominoes.UnaryPointTable
