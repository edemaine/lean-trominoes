/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierKeyCompactAtomWordData
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler from guarded carrier keys to compact terminal atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace GuardedCarrierKeyCompactAtomWords

open Computability Turing

inductive Control
  | between
  | firstBit
  | retain
  | discard
  deriving DecidableEq, Fintype, Inhabited

/-- Discard false-headed sentinel words. For a true-headed active word,
replace that support bit by the compact terminal constructor `00` and copy
the remaining carrier-key payload. -/
def transition : Control → DelimitedBinaryWords.Token →
    Control × List DelimitedBinaryWords.Token
  | .between, .wordStart => (.firstBit, [])
  | .firstBit, .bit true =>
      (.retain, [.wordStart, .bit false, .bit false])
  | .firstBit, .bit false => (.discard, [])
  | .firstBit, .wordEnd => (.between, [])
  | .retain, .wordEnd => (.between, [.wordEnd])
  | .retain, token => (.retain, [token])
  | .discard, .wordEnd => (.between, [])
  | .discard, _ => (.discard, [])
  | control, _ => (control, [])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

def tokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output .between transition finish source

/-- Semantic delimited-word transformation. -/
def compact (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨words input.words⟩

private theorem scan_retain_bits (bits : List Bool) :
    FiniteStateTransducer.scan transition .retain
        (bits.map .bit ++ [.wordEnd]) =
      (.between, bits.map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

private theorem scan_discard_bits (bits : List Bool) :
    FiniteStateTransducer.scan transition .discard
        (bits.map .bit ++ [.wordEnd]) =
      (.between, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_wordTokens (bits : List Bool) :
    FiniteStateTransducer.scan transition .between
        (DelimitedBinaryWords.wordTokens bits) =
      (.between, DelimitedBinaryWords.encode ⟨word bits⟩) := by
  cases bits with
  | nil => rfl
  | cons first bits =>
      cases first
      · unfold DelimitedBinaryWords.wordTokens DelimitedBinaryWords.encode word
        simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, transition]
        rw [scan_discard_bits]
        rfl
      · unfold DelimitedBinaryWords.wordTokens DelimitedBinaryWords.encode word
        simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, transition]
        rw [scan_retain_bits]
        simp [DelimitedBinaryWords.wordTokens]

theorem scan_encode (guarded : List (List Bool)) :
    FiniteStateTransducer.scan transition .between
        (DelimitedBinaryWords.encode ⟨guarded⟩) =
      (.between, DelimitedBinaryWords.encode ⟨words guarded⟩) := by
  induction guarded with
  | nil => rfl
  | cons guardedWord guarded induction =>
      unfold DelimitedBinaryWords.encode at induction ⊢
      rw [List.flatMap_cons, FiniteStateTransducer.scan_append,
        scan_wordTokens]
      dsimp
      rw [induction]
      simp [words, DelimitedBinaryWords.encode]

theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (compact input) := by
  rcases input with ⟨guarded⟩
  simp [tokens, compact, FiniteStateTransducer.output,
    scan_encode, finish]

/-- Physical token cleanup is polynomial-time. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteStateTransducer.computableInPolyTime
    (.between : Control) transition finish

/-- Sentinel removal and active-word retagging are a linear-time finite-state
pass over the delimited guarded-word stream. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode compact := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => tokens (DelimitedBinaryWords.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWords.finEncoding.encode tokensComputableInPolyTime
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    tokens_encode

end GuardedCarrierKeyCompactAtomWords
end PeriodicOrthocrossing
end LeanTrominoes

end
