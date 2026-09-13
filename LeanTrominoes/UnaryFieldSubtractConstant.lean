/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldHalveCompiler

/-! # Truncated subtraction of a fixed constant from unary fields -/

noncomputable section
namespace LeanTrominoes.UnaryFieldSubtractConstant
open Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)
open FiniteStateTransducer (scan output)

def initial (k : Nat) : Fin (k+1) := ⟨k,by omega⟩
def transition (k : Nat) (state : Fin (k+1)) : Symbol → Fin (k+1) × List Symbol
  | .delimiter => (initial k,[.delimiter])
  | .unit => (⟨state.val-1,by have := state.isLt; omega⟩,if state.val = 0 then [.unit] else [])
def finish {k : Nat} (_ : Fin (k+1)) : List Symbol := []

theorem scan_field (k n : Nat) (state : Fin (k+1)) :
    scan (transition k) state (unaryField n) = (initial k,unaryField (n-state.val)) := by
  induction n generalizing state with
  | zero => simp [unaryField,scan,transition]
  | succ n ih =>
    simp only [unaryField,List.replicate_succ,List.cons_append,scan,transition]
    rw [show scan (transition k) ⟨state.val-1,by have := state.isLt; omega⟩
      (List.replicate n Symbol.unit ++ [Symbol.delimiter]) =
      (initial k,unaryField (n-(state.val-1))) from ih _]
    by_cases h : state.val = 0
    · simp [h,unaryField,List.replicate_succ]
    · have he : n+1-state.val = n-(state.val-1) := by omega
      simp [h,he,unaryField]

theorem scan_fields (k : Nat) (values : List Nat) :
    scan (transition k) (initial k) (unaryFields values) =
      (initial k,unaryFields (values.map (·-k))) := by
  induction values with
  | nil => rfl
  | cons n values ih =>
    rw [UnaryFieldEncoderMachine.unaryFields_cons,FiniteStateTransducer.scan_append,scan_field]
    simp only [List.map_cons,UnaryFieldEncoderMachine.unaryFields_cons]
    rw [ih]
    rfl

def computableInPolyTime (k : Nat) : TM2ComputableInPolyTime unaryFields unaryFields (fun values => values.map (·-k)) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteStateTransducer.computableInPolyTime (initial k) (transition k) finish) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw
    (fun values => by simp [output,scan_fields,finish])

end LeanTrominoes.UnaryFieldSubtractConstant
