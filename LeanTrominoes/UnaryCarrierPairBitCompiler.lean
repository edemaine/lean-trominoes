/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Decoding sparse carrier-pair bit codes -/

noncomputable section

namespace LeanTrominoes.UnaryCarrierPairBits

open Computability Turing

/-- Zero suppresses a pair; one through four encode `(axis, nextSlice)` in
binary significance order. -/
def pair? : Nat → Option (Bool × Bool)
  | 0 => none
  | 1 => some (false, false)
  | 2 => some (true, false)
  | 3 => some (false, true)
  | _ + 4 => some (true, true)

def pairs (values : List Nat) : List (Bool × Bool) :=
  values.filterMap pair?

inductive Count
  | zero
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype

def Count.increment : Count → Count
  | .zero => .one
  | .one => .two
  | .two => .three
  | .three | .four => .four

def Count.pair? : Count → Option (Bool × Bool)
  | .zero => none
  | .one => some (false, false)
  | .two => some (true, false)
  | .three => some (false, true)
  | .four => some (true, true)

def transition :
    Count → UnaryFieldEncoderMachine.Symbol →
      Count × List (Bool × Bool)
  | count, .unit => (count.increment, [])
  | count, .delimiter => (.zero, count.pair?.toList)

def finish (_ : Count) : List (Bool × Bool) := []

def tokens (source : List UnaryFieldEncoderMachine.Symbol) :
    List (Bool × Bool) :=
  FiniteStateTransducer.output .zero transition finish source

private theorem scan_four (value : Nat) :
    FiniteStateTransducer.scan transition .four
        (List.replicate value .unit ++ [.delimiter]) =
      (.zero, [(true, true)]) := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition, Count.increment]
      exact induction

private theorem scan_unaryField (value : Nat) :
    FiniteStateTransducer.scan transition .zero
        (UnaryFieldEncoderMachine.unaryField value) =
      (.zero, (pair? value).toList) := by
  cases value with
  | zero => rfl
  | succ value =>
      cases value with
      | zero => rfl
      | succ value =>
          cases value with
          | zero => rfl
          | succ value =>
              cases value with
              | zero => rfl
              | succ value =>
                  simp only [UnaryFieldEncoderMachine.unaryField,
                    List.replicate_succ, List.cons_append,
                    FiniteStateTransducer.scan, transition,
                    Count.increment, pair?]
                  rw [scan_four]
                  rfl

private theorem scan_unaryFields (values : List Nat) :
    FiniteStateTransducer.scan transition .zero
        (UnaryFieldEncoderMachine.unaryFields values) =
      (.zero, pairs values) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      simp only [pairs, List.filterMap_cons]
      rw [induction]
      cases pair? value <;> rfl

private theorem tokens_unaryFields (values : List Nat) :
    tokens (UnaryFieldEncoderMachine.unaryFields values) = pairs values := by
  simp [tokens, FiniteStateTransducer.output, scan_unaryFields, finish]

/-- Sparse unary carrier-pair codes are decoded by a fixed finite-state
transduction and hence in polynomial time. -/
noncomputable def pairsComputableInPolyTime :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id pairs :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      Count.zero transition finish)
    (fun _ => rfl) tokens_unaryFields

end LeanTrominoes.UnaryCarrierPairBits

end
