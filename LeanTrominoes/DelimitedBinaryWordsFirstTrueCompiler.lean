/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Keeping only the first true bit of every binary word -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordsFirstTrue

open Computability Turing

/-- `none` is between words; `some seen` records whether the current word
has already contained a true bit. -/
abbrev Control := Option Bool

def transition : Control → DelimitedBinaryWords.Token →
    Control × List DelimitedBinaryWords.Token
  | none, .wordStart => (some false, [.wordStart])
  | some seen, .bit bit =>
      (some (seen || bit), [.bit (bit && !seen)])
  | some _, .wordEnd => (none, [.wordEnd])
  | control, token => (control, [token])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

/-- Clear every true bit after the first true bit. -/
def rowAux : Bool → List Bool → List Bool
  | _, [] => []
  | seen, bit :: bits =>
      (bit && !seen) :: rowAux (seen || bit) bits

def row (bits : List Bool) : List Bool := rowAux false bits

def rows (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.words.map row⟩

def tokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output none transition finish source

private theorem scan_bits (seen : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan transition (some seen)
        (bits.map .bit ++ [.wordEnd]) =
      (none, (rowAux seen bits).map .bit ++ [.wordEnd]) := by
  induction bits generalizing seen with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition, rowAux]
      rw [induction]
      rfl

theorem scan_wordTokens (bits : List Bool) :
    FiniteStateTransducer.scan transition none
        (DelimitedBinaryWords.wordTokens bits) =
      (none, DelimitedBinaryWords.wordTokens (row bits)) := by
  unfold DelimitedBinaryWords.wordTokens row
  simp only [FiniteStateTransducer.scan, transition]
  rw [scan_bits]
  rfl

theorem scan_encode (words : List (List Bool)) :
    FiniteStateTransducer.scan transition none
        (DelimitedBinaryWords.encode ⟨words⟩) =
      (none, DelimitedBinaryWords.encode ⟨words.map row⟩) := by
  induction words with
  | nil => rfl
  | cons bits words induction =>
      unfold DelimitedBinaryWords.encode at induction ⊢
      rw [List.flatMap_cons, FiniteStateTransducer.scan_append,
        scan_wordTokens]
      dsimp
      rw [induction]
      rfl

theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (rows input) := by
  rcases input with ⟨words⟩
  simp [tokens, FiniteStateTransducer.output, scan_encode, finish, rows]

/-- Keeping one true position per row is a linear-time finite-state pass. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode rows := by
  let compiler := FiniteStateTransducer.computableInPolyTime
    (none : Control) transition finish
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => tokens (DelimitedBinaryWords.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWords.finEncoding.encode compiler
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    tokens_encode

end DelimitedBinaryWordsFirstTrue
end LeanTrominoes

end
