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
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary fields as length-coded binary words -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldBinaryWords

open Computability Turing

/-- Represent a unary natural by an all-false binary word of the same length. -/
def word (value : Nat) : List Bool :=
  List.replicate value false

/-- Represent every unary field by one independently delimited length word. -/
def words (values : List Nat) : DelimitedBinaryWords.Input :=
  ⟨values.map word⟩

inductive Control
  | fieldStart
  | fieldBody
  deriving DecidableEq, Fintype

/-- Insert binary-word boundaries while replacing unary units by false bits. -/
def transition : Control → UnaryFieldEncoderMachine.Symbol →
    Control × List DelimitedBinaryWords.Token
  | .fieldStart, .unit =>
      (.fieldBody, [.wordStart, .bit false])
  | .fieldStart, .delimiter =>
      (.fieldStart, [.wordStart, .wordEnd])
  | .fieldBody, .unit =>
      (.fieldBody, [.bit false])
  | .fieldBody, .delimiter =>
      (.fieldStart, [.wordEnd])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

def tokens (source : List UnaryFieldEncoderMachine.Symbol) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output .fieldStart transition finish source

theorem scan_fieldBody (value : Nat) :
    FiniteStateTransducer.scan transition .fieldBody
        (List.replicate value .unit ++ [.delimiter]) =
      (.fieldStart,
        (List.replicate value false).map .bit ++ [.wordEnd]) := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction]
      simp [List.replicate_succ]

theorem scan_unaryField (value : Nat) :
    FiniteStateTransducer.scan transition .fieldStart
        (UnaryFieldEncoderMachine.unaryField value) =
      (.fieldStart, DelimitedBinaryWords.wordTokens (word value)) := by
  cases value with
  | zero => rfl
  | succ value =>
      simp only [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append,
        FiniteStateTransducer.scan, transition]
      rw [scan_fieldBody]
      rfl

theorem scan_unaryFields (values : List Nat) :
    FiniteStateTransducer.scan transition .fieldStart
        (UnaryFieldEncoderMachine.unaryFields values) =
      (.fieldStart, DelimitedBinaryWords.encode (words values)) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp
      rw [induction]
      rfl

theorem tokens_unaryFields (values : List Nat) :
    tokens (UnaryFieldEncoderMachine.unaryFields values) =
      DelimitedBinaryWords.encode (words values) := by
  simp [tokens, FiniteStateTransducer.output, scan_unaryFields, finish]

/-- Converting delimiter-encoded unary fields to their length-word view is
linear-time, so it can prepare any later word-pair comparison pipeline. -/
noncomputable def wordsComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      DelimitedBinaryWords.finEncoding.encode words := by
  let physical : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun values => tokens
        (UnaryFieldEncoderMachine.unaryFields values)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields
      (FiniteStateTransducer.computableInPolyTime
        Control.fieldStart transition finish)
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := DelimitedBinaryWords.finEncoding.encode)
    (function₂ := words) physical tokens_unaryFields

end UnaryFieldBinaryWords
end LeanTrominoes

end
