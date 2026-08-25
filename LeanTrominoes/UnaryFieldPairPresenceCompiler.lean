/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Row- and column-presence bits for unary-field products -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldPairPresence

open Computability Turing
open DelimitedBinaryWordPairs

inductive Side
  | first
  | second
  deriving DecidableEq, Fintype

def present : Side → (List Bool × List Bool) → Bool
  | .first, pair => !pair.1.isEmpty
  | .second, pair => !pair.2.isEmpty

def bits (side : Side) (input : DelimitedBinaryWordPairs.Input) :
    List Bool :=
  input.pairs.map (present side)

def transition (side : Side) :
    Bool → DelimitedBinaryWordPairs.Token → Bool × List Bool
  | _, .pairStart => (false, [])
  | seen, .middle => (seen, [])
  | seen, .pairEnd => (false, [seen])
  | seen, .firstBit _ =>
      match side with
      | .first => (true, [])
      | .second => (seen, [])
  | seen, .secondBit _ =>
      match side with
      | .first => (seen, [])
      | .second => (true, [])

def finish (_ : Bool) : List Bool := []

def tokens (side : Side) (source : List DelimitedBinaryWordPairs.Token) :
    List Bool :=
  FiniteStateTransducer.output false (transition side) finish source

theorem scan_firstBits_first (seen : Bool) (word : List Bool) :
    FiniteStateTransducer.scan (transition .first) seen
        (word.map .firstBit) =
      (seen || !word.isEmpty, []) := by
  induction word generalizing seen with
  | nil => cases seen <;> rfl
  | cons bit word induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      simpa using induction true

theorem scan_firstBits_second (seen : Bool) (word : List Bool) :
    FiniteStateTransducer.scan (transition .second) seen
        (word.map .firstBit) = (seen, []) := by
  induction word generalizing seen with
  | nil => rfl
  | cons bit word induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      simpa using induction seen

theorem scan_secondBits_first (seen : Bool) (word : List Bool) :
    FiniteStateTransducer.scan (transition .first) seen
        (word.map .secondBit) = (seen, []) := by
  induction word generalizing seen with
  | nil => rfl
  | cons bit word induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      simpa using induction seen

theorem scan_secondBits_second (seen : Bool) (word : List Bool) :
    FiniteStateTransducer.scan (transition .second) seen
        (word.map .secondBit) =
      (seen || !word.isEmpty, []) := by
  induction word generalizing seen with
  | nil => cases seen <;> rfl
  | cons bit word induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      simpa using induction true

theorem scan_pairTokens (side : Side)
    (pair : List Bool × List Bool) :
    FiniteStateTransducer.scan (transition side) false
        (DelimitedBinaryWordPairs.pairTokens pair) =
      (false, [present side pair]) := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    simp only [DelimitedBinaryWordPairs.pairTokens,
      FiniteStateTransducer.scan, transition,
      FiniteStateTransducer.scan_append]
  · rw [scan_firstBits_first, scan_secondBits_first]
    rfl
  · rw [scan_firstBits_second, scan_secondBits_second]
    rfl

theorem scan_encode (side : Side)
    (pairs : List (List Bool × List Bool)) :
    FiniteStateTransducer.scan (transition side) false
        (DelimitedBinaryWordPairs.encode ⟨pairs⟩) =
      (false, pairs.map (present side)) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [show DelimitedBinaryWordPairs.encode ⟨pair :: pairs⟩ =
        DelimitedBinaryWordPairs.pairTokens pair ++
          DelimitedBinaryWordPairs.encode ⟨pairs⟩ by rfl]
      rw [FiniteStateTransducer.scan_append, scan_pairTokens]
      dsimp
      rw [induction]

theorem tokens_encode (side : Side)
    (input : DelimitedBinaryWordPairs.Input) :
    tokens side (DelimitedBinaryWordPairs.encode input) = bits side input := by
  rcases input with ⟨pairs⟩
  simp [tokens, bits, FiniteStateTransducer.output,
    scan_encode, finish]

noncomputable def bitsComputableInPolyTime (side : Side) :
    TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode id (bits side) :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWordPairs.finEncoding.encode
    (FiniteStateTransducer.computableInPolyTime
      false (transition side) finish)
    (fun _ => rfl) (tokens_encode side)

/-- Presence of the selected member of every ordered unary-field pair. -/
def fieldBits (side : Side) (values : List Nat) : List Bool :=
  bits side
    (DelimitedBinaryWordPairProductMachine.pairs
      (UnaryFieldBinaryWords.words values))

@[simp] theorem fieldBits_length (side : Side) (values : List Nat) :
    (fieldBits side values).length = values.length ^ 2 := by
  simp [fieldBits, bits, DelimitedBinaryWordPairProductMachine.pairs,
    UnaryFieldBinaryWords.words, Function.comp_def, pow_two]

noncomputable def fieldBitsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valueCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values)
    (side : Side) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => fieldBits side (values input)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    valueCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompiler := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let composed := TM2CompositionMachine.computableInPolyTime
    pairCompiler (bitsComputableInPolyTime side)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input => fieldBits side (values input))
    composed (fun _ => rfl)

end UnaryFieldPairPresence
end LeanTrominoes

end
