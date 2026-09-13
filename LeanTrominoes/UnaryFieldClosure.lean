/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ConstantValueCompiler

/-! # Unary-list output closure for arbitrary encoded source types -/

noncomputable section
namespace LeanTrominoes.UnaryFieldClosure
open Computability Turing
noncomputable def appendCompiler
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (first second : Source → List Nat)
    (firstCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields first)
    (secondCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields second) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => first source ++ second source) := by
  let firstTokens : TM2ComputableInPolyTime encodeSource id
      (fun source => UnaryFieldEncoderMachine.unaryFields (first source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      firstCompiler (fun _ => rfl)
  let secondTokens : TM2ComputableInPolyTime encodeSource id
      (fun source => UnaryFieldEncoderMachine.unaryFields (second source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      secondCompiler (fun _ => rfl)
  let appended := TM2ListAppend.computableInPolyTime
    firstTokens secondTokens
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    appended fun source =>
      (UnaryFieldEncoderMachine.unaryFields_append
        (first source) (second source)).symm


end LeanTrominoes.UnaryFieldClosure
