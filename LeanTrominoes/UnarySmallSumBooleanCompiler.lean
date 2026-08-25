/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Boolean operations from zero-, one-, or two-unit fields -/

noncomputable section

namespace LeanTrominoes
namespace UnarySmallSumBooleans

open Computability Turing

inductive Operation
  | conjunction
  | disjunction
  deriving DecidableEq, Fintype

def Operation.apply : Operation → Bool → Bool → Bool
  | .conjunction => fun first second => first && second
  | .disjunction => fun first second => first || second

/-- Interpret a unary sum of two Boolean values.  Inputs above two saturate
at the `true,true` case, though aligned Boolean inputs never reach them. -/
def sumBit (operation : Operation) : Nat → Bool
  | 0 => operation.apply false false
  | 1 => operation.apply true false
  | _ + 2 => operation.apply true true

def bits (operation : Operation) (values : List Nat) : List Bool :=
  values.map (sumBit operation)

inductive Count
  | zero
  | one
  | many
  deriving DecidableEq, Fintype

def Count.bit (operation : Operation) : Count → Bool
  | .zero => sumBit operation 0
  | .one => sumBit operation 1
  | .many => sumBit operation 2

def Count.increment : Count → Count
  | .zero => .one
  | .one | .many => .many

def transition (operation : Operation) :
    Count → UnaryFieldEncoderMachine.Symbol → Count × List Bool
  | count, .unit => (count.increment, [])
  | count, .delimiter => (.zero, [count.bit operation])

def finish (_ : Count) : List Bool := []

def tokens (operation : Operation)
    (source : List UnaryFieldEncoderMachine.Symbol) : List Bool :=
  FiniteStateTransducer.output .zero (transition operation) finish source

theorem scan_many (operation : Operation) (value : Nat) :
    FiniteStateTransducer.scan (transition operation) .many
        (List.replicate value .unit ++ [.delimiter]) =
      (.zero, [sumBit operation (value + 2)]) := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition, Count.increment]
      rw [induction]
      rfl

theorem scan_unaryField (operation : Operation) (value : Nat) :
    FiniteStateTransducer.scan (transition operation) .zero
        (UnaryFieldEncoderMachine.unaryField value) =
      (.zero, [sumBit operation value]) := by
  cases value with
  | zero => rfl
  | succ value =>
      cases value with
      | zero => rfl
      | succ value =>
          simp only [UnaryFieldEncoderMachine.unaryField,
            List.replicate_succ, List.cons_append,
            FiniteStateTransducer.scan, transition, Count.increment]
          rw [scan_many]
          rfl

theorem scan_unaryFields (operation : Operation) (values : List Nat) :
    FiniteStateTransducer.scan (transition operation) .zero
        (UnaryFieldEncoderMachine.unaryFields values) =
      (.zero, bits operation values) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp
      rw [induction]
      rfl

theorem tokens_unaryFields (operation : Operation) (values : List Nat) :
    tokens operation (UnaryFieldEncoderMachine.unaryFields values) =
      bits operation values := by
  simp [tokens, FiniteStateTransducer.output,
    scan_unaryFields, finish]

/-- Reading each small unary sum and applying conjunction or disjunction is
a fixed finite-state transduction. -/
noncomputable def bitsComputableInPolyTime (operation : Operation) :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id
      (bits operation) :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      Count.zero (transition operation) finish)
    (fun _ => rfl) (tokens_unaryFields operation)

end UnarySmallSumBooleans
end LeanTrominoes

end
