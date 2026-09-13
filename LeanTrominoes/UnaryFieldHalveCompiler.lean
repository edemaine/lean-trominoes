/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Fixed-factor division of unary coordinate fields -/

noncomputable section
namespace LeanTrominoes.UnaryFieldHalve
open Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)
open FiniteStateTransducer (scan output)

def transition : Bool → Symbol → Bool × List Symbol
  | pending, .unit => (!pending, if pending then [.unit] else [])
  | _, .delimiter => (false,[.delimiter])
def finish (_ : Bool) : List Symbol := []
def tokens := output false transition finish

theorem scan_field (n : Nat) :
    scan transition false (unaryField n) = (false,unaryField (n/2)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        have h := ih n (by omega)
        have hn : (n+1+1)/2 = n/2+1 := by omega
        simp only [unaryField,List.replicate_succ,List.cons_append,scan,transition,
          Bool.not_false,Bool.false_eq_true,↓reduceIte,List.nil_append,Bool.not_true]
        rw [show scan transition false (List.replicate n Symbol.unit ++ [Symbol.delimiter]) =
          (false,unaryField (n/2)) from h]
        simp [unaryField,hn,List.replicate_succ]

theorem scan_fields (values : List Nat) :
    scan transition false (unaryFields values) = (false,unaryFields (values.map (·/2))) := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    rw [UnaryFieldEncoderMachine.unaryFields_cons,FiniteStateTransducer.scan_append,scan_field]
    simp only [List.map_cons,UnaryFieldEncoderMachine.unaryFields_cons]
    rw [ih]

def computableInPolyTime : TM2ComputableInPolyTime unaryFields unaryFields (fun values => values.map (·/2)) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteStateTransducer.computableInPolyTime false transition finish) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw
    (fun values => by simp [output,scan_fields,finish])

end LeanTrominoes.UnaryFieldHalve
