/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.TM2NativeListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time closure under appending delimited binary words -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWords

open Computability Turing

/-- Append the semantic word lists of two delimited inputs. -/
def append (first second : Input) : Input :=
  ⟨first.words ++ second.words⟩

@[simp] theorem append_words (first second : Input) :
    (append first second).words = first.words ++ second.words :=
  rfl

theorem encode_append (first second : Input) :
    encode (append first second) = encode first ++ encode second := by
  simp [append, encode, List.flatMap_append]

/-- Equality of semantic word lists determines equality of delimited-word
inputs without unfolding the words themselves. -/
theorem eq_of_words_eq {first second : Input}
    (wordsEq : first.words = second.words) : first = second := by
  cases first with
  | mk firstWords =>
      cases second with
      | mk secondWords =>
          exact congrArg Input.mk wordsEq

/-- Two canonically encoded delimited-word outputs on the same native-list
input can be appended in polynomial time, including empty input alphabets. -/
noncomputable def appendComputableInPolyTime
    {InputSymbol : Type} [Fintype InputSymbol]
    {first second : List InputSymbol → Input}
    (firstCompiler :
      @TM2ComputableInPolyTime
        (List InputSymbol) Input InputSymbol Token
        id finEncoding.encode first)
    (secondCompiler :
      @TM2ComputableInPolyTime
        (List InputSymbol) Input InputSymbol Token
        id finEncoding.encode second) :
    @TM2ComputableInPolyTime
      (List InputSymbol) Input InputSymbol Token
      id finEncoding.encode (fun input => append (first input) (second input)) := by
  let firstTokens :
      @TM2ComputableInPolyTime
        (List InputSymbol) (List Token) InputSymbol Token
        id id (fun input => finEncoding.encode (first input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      firstCompiler (fun _input => rfl)
  let secondTokens :
      @TM2ComputableInPolyTime
        (List InputSymbol) (List Token) InputSymbol Token
        id id (fun input => finEncoding.encode (second input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      secondCompiler (fun _input => rfl)
  let appended := TM2ListAppend.nativeComputableInPolyTime
    firstTokens secondTokens
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
    appended fun input => by
      rw [finEncoding_encode, finEncoding_encode, finEncoding_encode]
      exact (encode_append (first input) (second input)).symm

end DelimitedBinaryWords
end LeanTrominoes

end
