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

/-! # Replace active binary-word guards with a fixed constructor prefix -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordGuardedPrefix

open Computability Turing

inductive Control | between | guard | retain | discard
  deriving DecidableEq, Fintype
instance : Inhabited Control := ⟨.between⟩

def word (prefixBits : List Bool) : List Bool → List (List Bool)
  | true :: payload => [prefixBits ++ payload]
  | _ => []

def words (prefixBits : List Bool) (input : DelimitedBinaryWords.Input) : DelimitedBinaryWords.Input :=
  ⟨input.words.flatMap (word prefixBits)⟩

def transition (prefixBits : List Bool) : Control → DelimitedBinaryWords.Token →
    Control × List DelimitedBinaryWords.Token
  | .between, .wordStart => (.guard, [])
  | .guard, .bit true => (.retain, .wordStart :: prefixBits.map .bit)
  | .guard, .bit false => (.discard, [])
  | .guard, .wordEnd => (.between, [])
  | .retain, .wordEnd => (.between, [.wordEnd])
  | .retain, token => (.retain, [token])
  | .discard, .wordEnd => (.between, [])
  | .discard, _ => (.discard, [])
  | control, _ => (control, [])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

def tokens (prefixBits : List Bool) (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output .between (transition prefixBits) finish source

private theorem scan_retain_bits (prefixBits bits : List Bool) :
    FiniteStateTransducer.scan (transition prefixBits) .retain (bits.map .bit ++ [.wordEnd]) =
      (.between, bits.map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append, FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

private theorem scan_discard_bits (prefixBits bits : List Bool) :
    FiniteStateTransducer.scan (transition prefixBits) .discard (bits.map .bit ++ [.wordEnd]) =
      (.between, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append, FiniteStateTransducer.scan, transition]
      exact induction

private theorem scan_wordTokens (prefixBits bits : List Bool) :
    FiniteStateTransducer.scan (transition prefixBits) .between
        (DelimitedBinaryWords.wordTokens bits) =
      (.between, DelimitedBinaryWords.encode ⟨word prefixBits bits⟩) := by
  cases bits with
  | nil => rfl
  | cons first bits =>
      cases first
      · unfold DelimitedBinaryWords.wordTokens DelimitedBinaryWords.encode word
        simp only [List.map_cons, List.cons_append, FiniteStateTransducer.scan, transition]
        rw [scan_discard_bits]
        rfl
      · unfold DelimitedBinaryWords.wordTokens DelimitedBinaryWords.encode word
        simp only [List.map_cons, List.cons_append, FiniteStateTransducer.scan, transition]
        rw [scan_retain_bits]
        simp [DelimitedBinaryWords.wordTokens, List.append_assoc]

private theorem scan_encode (prefixBits : List Bool) (guarded : List (List Bool)) :
    FiniteStateTransducer.scan (transition prefixBits) .between (DelimitedBinaryWords.encode ⟨guarded⟩) =
      (.between, DelimitedBinaryWords.encode (words prefixBits ⟨guarded⟩)) := by
  induction guarded with
  | nil => rfl
  | cons guardedWord guarded induction =>
      unfold DelimitedBinaryWords.encode at induction ⊢
      rw [List.flatMap_cons, FiniteStateTransducer.scan_append, scan_wordTokens]
      dsimp
      rw [induction]
      simp [words, DelimitedBinaryWords.encode]

@[simp] theorem tokens_encode (prefixBits : List Bool) (input : DelimitedBinaryWords.Input) :
    tokens prefixBits (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (words prefixBits input) := by
  rcases input with ⟨guarded⟩
  simp [tokens, FiniteStateTransducer.output, scan_encode, finish]

/-- Guard replacement and rejection removal require only a finite-state pass. -/
noncomputable def tokensComputableInPolyTime (prefixBits : List Bool) :
    TM2ComputableInPolyTime id id (tokens prefixBits) :=
  FiniteStateTransducer.computableInPolyTime (.between : Control) (transition prefixBits) finish

noncomputable def computableInPolyTime (prefixBits : List Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode (words prefixBits) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.finEncoding.encode (tokensComputableInPolyTime prefixBits)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical (tokens_encode prefixBits)

end LeanTrominoes.DelimitedBinaryWordGuardedPrefix

end
