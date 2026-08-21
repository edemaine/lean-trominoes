/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary true counts of delimiter-encoded Boolean words -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordTrueCounts

open Computability Turing

def countTrue (word : List Bool) : Nat := word.count true

def counts (input : DelimitedBinaryWords.Input) : List Nat :=
  input.words.map countTrue

def block : DelimitedBinaryWords.Token →
    List UnaryFieldEncoderMachine.Symbol
  | .wordStart => []
  | .bit false => []
  | .bit true => [.unit]
  | .wordEnd => [.delimiter]

theorem flatMap_block_bits (bits : List Bool) :
    (bits.map DelimitedBinaryWords.Token.bit).flatMap block =
      List.replicate (bits.count true) .unit := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simp [block, induction, List.replicate_succ]

theorem flatMap_block_wordTokens (word : List Bool) :
    (DelimitedBinaryWords.wordTokens word).flatMap block =
      UnaryFieldEncoderMachine.unaryField (countTrue word) := by
  simp [DelimitedBinaryWords.wordTokens, List.flatMap_append,
    flatMap_block_bits, UnaryFieldEncoderMachine.unaryField, countTrue,
    block]

theorem flatMap_block_encode (input : DelimitedBinaryWords.Input) :
    (DelimitedBinaryWords.encode input).flatMap block =
      UnaryFieldEncoderMachine.unaryFields (counts input) := by
  rcases input with ⟨words⟩
  induction words with
  | nil => rfl
  | cons word words induction =>
      have rest :
          (words.flatMap DelimitedBinaryWords.wordTokens).flatMap block =
            UnaryFieldEncoderMachine.unaryFields
              (words.map countTrue) := by
        simpa only [DelimitedBinaryWords.encode, counts] using induction
      simp only [DelimitedBinaryWords.encode, List.flatMap_cons,
        List.flatMap_append, flatMap_block_wordTokens, counts,
        List.map_cons, UnaryFieldEncoderMachine.unaryFields_cons]
      rw [rest]

/-- Counting every row's true bits into delimiter-terminated unary fields is
linear time in the delimiter encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields counts := by
  let physical := FiniteBlockTransducer.computableInPolyTime block
  refine
    { tm := physical.tm
      inputAlphabet := physical.inputAlphabet
      outputAlphabet := physical.outputAlphabet
      time := physical.time
      outputsFun := ?_ }
  intro input
  have run := physical.outputsFun (DelimitedBinaryWords.encode input)
  simpa only [DelimitedBinaryWords.finEncoding, id_eq,
    flatMap_block_encode] using run

end DelimitedBinaryWordTrueCounts
end LeanTrominoes

end
