/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldHalveCompiler

/-! # Finite residue lookup on unary fields -/
noncomputable section
namespace LeanTrominoes.UnaryFieldResidue
open Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)
open FiniteStateTransducer (scan output)

variable (modulus : Nat) (positive : 0 < modulus)
def zero : Fin modulus := ⟨0,positive⟩
def step (r : Fin modulus) : Fin modulus := ⟨(r.val+1)%modulus,Nat.mod_lt _ positive⟩
def transition (table : Fin modulus → Nat) : Fin modulus → Symbol → Fin modulus × List Symbol
  | r,.unit => (step modulus positive r,[])
  | r,.delimiter => (zero modulus positive,unaryField (table r))
def finish (_ : Fin modulus) : List Symbol := []

theorem scan_units (table : Fin modulus → Nat) (n : Nat) (r : Fin modulus) :
    scan (transition modulus positive table) r (List.replicate n Symbol.unit) =
      (⟨(r.val+n)%modulus,Nat.mod_lt _ positive⟩,[]) := by
  induction n generalizing r with
  | zero => simp [scan,Nat.mod_eq_of_lt r.isLt]
  | succ n ih =>
    simp only [List.replicate_succ,scan,transition,List.nil_append,ih]
    congr 1
    apply Fin.ext
    simp [step,Nat.add_mod,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem scan_field (table : Fin modulus → Nat) (n : Nat) :
    scan (transition modulus positive table) (zero modulus positive) (unaryField n) =
      (zero modulus positive,unaryField (table ⟨n%modulus,Nat.mod_lt _ positive⟩)) := by
  rw [unaryField,FiniteStateTransducer.scan_append,scan_units]
  simp [scan,transition,zero]

theorem scan_fields (table : Fin modulus → Nat) (ns : List Nat) :
    scan (transition modulus positive table) (zero modulus positive) (unaryFields ns) =
      (zero modulus positive,unaryFields (ns.map fun n => table ⟨n%modulus,Nat.mod_lt _ positive⟩)) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    rw [UnaryFieldEncoderMachine.unaryFields_cons,FiniteStateTransducer.scan_append,scan_field]
    simp only [List.map_cons,UnaryFieldEncoderMachine.unaryFields_cons]
    rw [ih]

def computableInPolyTime (table : Fin modulus → Nat) :
    TM2ComputableInPolyTime unaryFields unaryFields
      (fun ns => ns.map fun n => table ⟨n%modulus,Nat.mod_lt _ positive⟩) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteStateTransducer.computableInPolyTime (zero modulus positive)
      (transition modulus positive table) (finish modulus)) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw
    (fun ns => by simp [output,scan_fields,finish])
end LeanTrominoes.UnaryFieldResidue
