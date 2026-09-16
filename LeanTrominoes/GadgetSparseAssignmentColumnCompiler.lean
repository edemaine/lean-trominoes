/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetSparseAssignmentTokens
import LeanTrominoes.UnaryFieldResidueCompiler
import LeanTrominoes.FiniteBlockTransducer

/-! # Polynomial-time unary columns of sparse drawing assignments -/
noncomputable section
namespace LeanTrominoes.GadgetSparseAssignmentColumns
open Computability Turing GadgetSparseAssignmentTokens
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)
open FiniteStateTransducer (scan output)

def transition (vertical : Bool) : Bool → Token → Bool × List Symbol
  | phase,.coordinateUnit => (phase,if phase = vertical then [.unit] else [])
  | _,.fieldEnd => (true,if vertical then [] else [.delimiter])
  | _,.cellType _ => (false,if vertical then [.delimiter] else [])
def finish (_ : Bool) : List Symbol := []

theorem scan_units (vertical phase : Bool) (n : Nat) :
    scan (transition vertical) phase (List.replicate n Token.coordinateUnit) =
      (phase,if phase = vertical then List.replicate n Symbol.unit else []) := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    simp only [List.replicate_succ,scan,transition,ih]
    split_ifs <;> simp

theorem scan_assignment (vertical : Bool) (a : Cell × Gadget.OrthogonalCellType) :
    scan (transition vertical) false (assignmentTokens a) =
      (false,unaryField (if vertical then a.1.2.toNat else a.1.1.toNat)) := by
  cases vertical <;>
    simp [assignmentTokens,List.append_assoc,FiniteStateTransducer.scan_append,scan_units,scan,transition,unaryField]

theorem scan_assignments (vertical : Bool) (assignments : List (Cell × Gadget.OrthogonalCellType)) :
    scan (transition vertical) false (assignmentsTokens assignments) =
      (false,unaryFields (assignments.map fun a => if vertical then a.1.2.toNat else a.1.1.toNat)) := by
  induction assignments with
  | nil => rfl
  | cons a assignments ih =>
    simp only [assignmentsTokens,List.flatMap_cons,List.map_cons]
    rw [FiniteStateTransducer.scan_append,scan_assignment]
    dsimp only
    simp only [assignmentsTokens] at ih
    rw [ih]
    rfl

/-- Canonical assignment records compile to either natural-coordinate column. -/
def coordinateCompiler (vertical : Bool) :
    TM2ComputableInPolyTime assignmentsTokens unaryFields
      (fun assignments => assignments.map fun a => if vertical then a.1.2.toNat else a.1.1.toNat) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare assignmentsTokens
    (FiniteStateTransducer.computableInPolyTime false (transition vertical) finish)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw
    (fun assignments => by simp [output,scan_assignments,finish])

def typeBlock (value : Gadget.OrthogonalCellType → Nat) : Token → List Symbol
  | .cellType kind => unaryField (value kind)
  | _ => []

theorem type_assignments (value : Gadget.OrthogonalCellType → Nat)
    (assignments : List (Cell × Gadget.OrthogonalCellType)) :
    (assignmentsTokens assignments).flatMap (typeBlock value) =
      unaryFields (assignments.map fun a => value a.2) := by
  induction assignments with
  | nil => rfl
  | cons a assignments ih =>
    simp [assignmentsTokens,assignmentTokens,List.flatMap_append,List.flatMap_replicate,typeBlock,unaryFields] at ih ⊢
    exact ih

def typeCompiler (value : Gadget.OrthogonalCellType → Nat) :
    TM2ComputableInPolyTime assignmentsTokens unaryFields
      (fun assignments => assignments.map fun a => value a.2) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare assignmentsTokens
    (FiniteBlockTransducer.computableInPolyTime (typeBlock value)) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw (type_assignments value)
end LeanTrominoes.GadgetSparseAssignmentColumns
