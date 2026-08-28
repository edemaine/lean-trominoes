/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2NativeListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Polynomial-time closure under appending unary fields -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldEncoderMachine

open Computability Turing

/-- Two unary-encoded natural-list outputs on the same native-list input can
be appended in polynomial time, including empty input alphabets. -/
noncomputable def appendComputableInPolyTime
    {InputSymbol : Type} [Fintype InputSymbol]
    {first second : List InputSymbol → List Nat}
    (firstCompiler :
      @TM2ComputableInPolyTime
        (List InputSymbol) (List Nat)
        InputSymbol Symbol id unaryFields first)
    (secondCompiler :
      @TM2ComputableInPolyTime
        (List InputSymbol) (List Nat)
        InputSymbol Symbol id unaryFields second) :
    @TM2ComputableInPolyTime
      (List InputSymbol) (List Nat)
      InputSymbol Symbol id unaryFields
      (fun input => first input ++ second input) := by
  let firstTokens :
      @TM2ComputableInPolyTime
        (List InputSymbol) (List Symbol)
        InputSymbol Symbol id id
        (fun input => unaryFields (first input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      firstCompiler (fun _input => rfl)
  let secondTokens :
      @TM2ComputableInPolyTime
        (List InputSymbol) (List Symbol)
        InputSymbol Symbol id id
        (fun input => unaryFields (second input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      secondCompiler (fun _input => rfl)
  let appended := TM2ListAppend.nativeComputableInPolyTime
    firstTokens secondTokens
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
    appended fun input => (unaryFields_append
      (first input) (second input)).symm

end UnaryFieldEncoderMachine
end LeanTrominoes

end
