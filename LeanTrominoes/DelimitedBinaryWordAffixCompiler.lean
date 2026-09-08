/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Fixed prefixes and suffixes on delimited binary words -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordAffix

open Computability Turing

/-- Add the same finite context to every word, including empty words. -/
def words (prefixBits suffixBits : List Bool) (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.words.map fun word => prefixBits ++ word ++ suffixBits⟩

def block (prefixBits suffixBits : List Bool) : DelimitedBinaryWords.Token →
    List DelimitedBinaryWords.Token
  | .wordStart => .wordStart :: prefixBits.map .bit
  | .bit value => [.bit value]
  | .wordEnd => suffixBits.map .bit ++ [.wordEnd]

private theorem bits_flatMap (prefixBits suffixBits bits : List Bool) :
    (bits.map DelimitedBinaryWords.Token.bit).flatMap (block prefixBits suffixBits) =
      bits.map DelimitedBinaryWords.Token.bit := by
  induction bits with
  | nil => rfl
  | cons bit bits induction => simp [block, induction]

theorem wordTokens_flatMap (prefixBits suffixBits bits : List Bool) :
    (DelimitedBinaryWords.wordTokens bits).flatMap (block prefixBits suffixBits) =
      DelimitedBinaryWords.wordTokens (prefixBits ++ bits ++ suffixBits) := by
  simp [DelimitedBinaryWords.wordTokens, List.flatMap_append,
    block, bits_flatMap, List.map_append, List.append_assoc]

theorem encode_flatMap (prefixBits suffixBits : List Bool) (input : DelimitedBinaryWords.Input) :
    (DelimitedBinaryWords.encode input).flatMap (block prefixBits suffixBits) =
      DelimitedBinaryWords.encode (words prefixBits suffixBits input) := by
  unfold DelimitedBinaryWords.encode words
  rw [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro bits _member
  exact wordTokens_flatMap prefixBits suffixBits bits

/-- A fixed prefix and suffix require only a finite block substitution. -/
noncomputable def computableInPolyTime (prefixBits suffixBits : List Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode (words prefixBits suffixBits) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.finEncoding.encode
    (FiniteBlockTransducer.computableInPolyTime (block prefixBits suffixBits))
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (encode_flatMap prefixBits suffixBits)

end LeanTrominoes.DelimitedBinaryWordAffix

end
