/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Splitting interleaved unary pairs into coordinate columns -/
noncomputable section
namespace LeanTrominoes.UnaryFieldPairProjection
open _root_.Computability Turing
open UnaryFieldEncoderMachine
open FiniteStateTransducer

def transition (second : Bool) (phase : Bool) : Symbol → Bool × List Symbol
  | .unit => (phase,if phase=second then [.unit] else [])
  | .delimiter => (!phase,if phase=second then [.delimiter] else [])

def tokens (second : Bool) := FiniteStateTransducer.output false (transition second) (fun _ => [])

def fields (pairs : List (Nat × Nat)) : List Nat := pairs.flatMap fun p => [p.1,p.2]
def values (second : Bool) (pairs : List (Nat × Nat)) : List Nat :=
  pairs.map fun p => if second then p.2 else p.1

private theorem scan_field (second phase : Bool) (n : Nat) :
    scan (transition second) phase (unaryField n) =
      (!phase,if phase=second then unaryField n else []) := by
  induction n with
  | zero => cases phase <;> cases second <;> rfl
  | succ n ih =>
    rw [unaryField,List.replicate_succ,List.cons_append]
    simp only [scan,transition]
    rw [← unaryField,ih]
    cases phase <;> cases second <;> rfl

private theorem scan_pairs (second : Bool) (pairs : List (Nat × Nat)) :
    scan (transition second) false (unaryFields (fields pairs)) =
      (false,unaryFields (values second pairs)) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    simp only [fields] at ih
    simp only [fields,List.flatMap_cons,unaryFields_append,unaryFields_cons,unaryFields_nil,
      List.append_nil,scan_append,scan_field]
    simp only [Bool.not_false,Bool.not_true]
    rw [ih]
    cases second <;> simp [values]

theorem tokens_pairs (second : Bool) (pairs : List (Nat × Nat)) :
    tokens second (unaryFields (fields pairs))=unaryFields (values second pairs) := by
  unfold tokens FiniteStateTransducer.output
  rw [scan_pairs]
  simp

def computableInPolyTime (second : Bool) :
    TM2ComputableInPolyTime (fun pairs => unaryFields (fields pairs)) unaryFields (values second) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare (fun pairs => unaryFields (fields pairs))
    (FiniteStateTransducer.computableInPolyTime false (transition second) (fun _ => []))
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared (tokens_pairs second)

end LeanTrominoes.UnaryFieldPairProjection
