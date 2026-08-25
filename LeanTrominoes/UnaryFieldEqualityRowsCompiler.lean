/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Equality matrices for unary natural fields -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldEqualityRows

open Computability Turing

/-- Flat row-major equality matrix of a unary natural column. -/
def equalityBits (values : List Nat) : List Bool :=
  DelimitedBinaryWordEqualitySquare.equalityBits
    (UnaryFieldBinaryWords.words values)

theorem equalityBits_eq_flatMap (values : List Nat) :
    equalityBits values =
      values.flatMap fun first =>
        values.map fun second => decide (first = second) := by
  unfold equalityBits
  rw [DelimitedBinaryWordEqualitySquare.equalityBits_eq_flatMap]
  unfold UnaryFieldBinaryWords.words
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, UnaryFieldBinaryWords.word]

@[simp] theorem equalityBits_length (values : List Nat) :
    (equalityBits values).length = values.length ^ 2 := by
  rw [equalityBits_eq_flatMap]
  simp [pow_two]

/-- Any unary-field compiler can be followed by the ordered equality-square
pipeline in polynomial time. -/
noncomputable def equalityBitsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valueCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => equalityBits (values input)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    valueCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let equalityCompiler :=
    DelimitedBinaryWordEqualitySquare.equalityBitsComputableInPolyTime
      encodeInput (fun input => UnaryFieldBinaryWords.words (values input))
      wordCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input => equalityBits (values input))
    equalityCompiler (fun _ => rfl)

end UnaryFieldEqualityRows
end LeanTrominoes

end
