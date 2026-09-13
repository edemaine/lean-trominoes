/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldClosure
import LeanTrominoes.UnaryFieldCartesian

/-! # Polynomial-time Cartesian products of independently compiled unary columns -/

noncomputable section
namespace LeanTrominoes.UnaryFieldCartesian
open Computability Turing
open UnaryFieldSquareProjection (Side choose)
open UnaryFieldEncoderMachine (unaryFields)

variable {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (encode : Source → List Symbol) (first second : Source → List Nat)
    (firstCompiler : TM2ComputableInPolyTime encode unaryFields first)
    (secondCompiler : TM2ComputableInPolyTime encode unaryFields second)

def tagsCompiler : TM2ComputableInPolyTime encode unaryFields
    (fun source => tags (first source) (second source)) := by
  let ones := TM2CompositionMachine.computableInPolyTime firstCompiler
    UnaryFieldConstantStreams.onesComputableInPolyTime
  let zeros := TM2CompositionMachine.computableInPolyTime secondCompiler
    UnaryFieldConstantStreams.zerosComputableInPolyTime
  exact UnaryFieldClosure.appendCompiler encode _ _ ones zeros

def controlsCompiler : TM2ComputableInPolyTime encode id
    (fun source => controls (first source) (second source)) := by
  let tagged := tagsCompiler encode first second firstCompiler secondCompiler
  let front := UnaryFieldPairPresence.fieldBitsComputableInPolyTime encode _ tagged .first
  let back := UnaryFieldPairPresence.fieldBitsComputableInPolyTime encode _ tagged .second
  let negated := AlignedBooleanListClosure.mapNegatedComputableInPolyTime encode _ back
  exact AlignedBooleanListClosure.combinedComputableInPolyTime encode .conjunction _ _
    (fun source => by simp [AlignedBooleanListClosure.negated]) front negated

def valuesCompiler (side : Side) : TM2ComputableInPolyTime encode unaryFields
    (fun source => values side (first source) (second source)) := by
  let joined := UnaryFieldClosure.appendCompiler encode _ _ firstCompiler secondCompiler
  let projected := TM2CompositionMachine.computableInPolyTime joined
    (UnaryFieldSquareProjection.computableInPolyTime side)
  exact UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime encode _ _
    (controlsCompiler encode first second firstCompiler secondCompiler) projected

/-- Project either entry of each ordered pair, including empty and repeated columns. -/
def computableInPolyTime (side : Side) : TM2ComputableInPolyTime encode unaryFields
    (fun source => (first source).flatMap fun a => (second source).map fun b => choose side a b) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (valuesCompiler encode first second firstCompiler secondCompiler side)
    (fun source => congrArg unaryFields (values_eq side (first source) (second source)))

end LeanTrominoes.UnaryFieldCartesian
