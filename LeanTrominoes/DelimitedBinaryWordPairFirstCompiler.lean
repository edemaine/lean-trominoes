/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # First components of adjacent delimited binary-word pairs -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordPairFirst

open Computability Turing

/-- Keep positions zero, two, four, and so on, including an unmatched last word. -/
def firstWords : List (List Bool) → List (List Bool)
  | first :: _second :: rest => first :: firstWords rest
  | [first] => [first]
  | [] => []

def first (input : DelimitedBinaryWords.Input) : DelimitedBinaryWords.Input :=
  ⟨firstWords input.words⟩

/-- Toggle the copy flag only at complete word boundaries. -/
def transition (copy : Bool) (token : DelimitedBinaryWords.Token) :
    Bool × List DelimitedBinaryWords.Token :=
  (if token = .wordEnd then !copy else copy, if copy then [token] else [])

def finish (_ : Bool) : List DelimitedBinaryWords.Token := []

def tokens (source : List DelimitedBinaryWords.Token) : List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output true transition finish source

private theorem scan_bits (copy : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan transition copy (bits.map .bit) =
      (copy, if copy then bits.map .bit else []) := by
  induction bits with
  | nil => cases copy <;> rfl
  | cons bit bits induction =>
      cases copy <;> simp [FiniteStateTransducer.scan, transition, induction]

private theorem scan_word (copy : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan transition copy (DelimitedBinaryWords.wordTokens bits) =
      (!copy, if copy then DelimitedBinaryWords.wordTokens bits else []) := by
  unfold DelimitedBinaryWords.wordTokens
  rw [FiniteStateTransducer.scan]
  simp only [transition, reduceCtorEq, ↓reduceIte]
  rw [FiniteStateTransducer.scan_append, scan_bits]
  cases copy <;> simp [FiniteStateTransducer.scan, transition]

private theorem scan_encode (words : List (List Bool)) :
    FiniteStateTransducer.scan transition true (DelimitedBinaryWords.encode ⟨words⟩) =
      (decide (words.length % 2 = 0), DelimitedBinaryWords.encode ⟨firstWords words⟩) := by
  induction words using firstWords.induct with
  | case1 first second rest induction =>
      simp only [DelimitedBinaryWords.encode, List.flatMap_cons]
      rw [FiniteStateTransducer.scan_append, scan_word]
      dsimp only [Bool.not_true]
      rw [FiniteStateTransducer.scan_append, scan_word]
      dsimp only [Bool.not_false]
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      change ((FiniteStateTransducer.scan transition true (DelimitedBinaryWords.encode ⟨rest⟩)).1,
        DelimitedBinaryWords.wordTokens first ++
          (FiniteStateTransducer.scan transition true (DelimitedBinaryWords.encode ⟨rest⟩)).2) =
        (_, DelimitedBinaryWords.encode ⟨first :: firstWords rest⟩)
      rw [induction]
      simp [DelimitedBinaryWords.encode]
      omega
  | case2 first =>
      simpa [DelimitedBinaryWords.encode, firstWords] using scan_word true first
  | case3 => rfl

@[simp] theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) = DelimitedBinaryWords.encode (first input) := by
  rcases input with ⟨words⟩
  simp [tokens, first, FiniteStateTransducer.output, scan_encode, finish]

/-- On paired inputs the alternating pass is exactly first-component projection. -/
@[simp] theorem first_componentWords (pairs : List (List Bool × List Bool)) :
    first (DelimitedBinaryWordGuardedPairMerge.componentWords pairs) =
      ⟨pairs.map Prod.fst⟩ := by
  unfold first DelimitedBinaryWordGuardedPairMerge.componentWords
  apply congrArg DelimitedBinaryWords.Input.mk
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simpa [firstWords] using congrArg (List.cons pair.1) induction

noncomputable def tokensComputableInPolyTime : TM2ComputableInPolyTime id id tokens :=
  FiniteStateTransducer.computableInPolyTime true transition finish

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode first := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.finEncoding.encode tokensComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical tokens_encode

end LeanTrominoes.DelimitedBinaryWordPairFirst

end
