/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPlacementColumnCompiler

/-! # Polynomial-time assembly of the actual unary strip-completion encoding -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]

structure PlacementListCompiler (placements : List Symbol → List (Placement Unit)) where
  fields : TM2ComputableInPolyTime id unaryFields (fun s => (placements s).flatMap CompletionStripEncoding.placementFields)
  count : ScalarCompiler (fun s => (placements s).length)

namespace PlacementListCompiler
variable {a b : List Symbol → List (Placement Unit)}

def ofEq (compiler : PlacementListCompiler a) (eq : ∀ s, a s = b s) : PlacementListCompiler b where
  fields := TM2ComputableInPolyTime.of_eq compiler.fields (fun s => by simp only [eq])
  count := TM2ComputableInPolyTime.of_eq compiler.count (fun s => by simp only [eq])

def append (ca : PlacementListCompiler a) (cb : PlacementListCompiler b) : PlacementListCompiler (fun s => a s ++ b s) where
  fields := TM2ComputableInPolyTime.of_eq
    (UnaryFieldClosure.appendCompiler id _ _ ca.fields cb.fields) (fun s => by simp)
  count := by
    let ac : Compiler (fun _ : List Symbol => [()]) (fun s _ => (a s).length) := ca.count
    let bc : Compiler (fun _ : List Symbol => [()]) (fun s _ => (b s).length) := cb.count
    exact TM2ComputableInPolyTime.of_eq (add ac bc) (fun s => by simp)
end PlacementListCompiler

private def booleanBlock : UnaryFieldEncoderMachine.Symbol → List Bool
  | .unit => [true]
  | .delimiter => [false]

private theorem boolean_fields (ns : List Nat) :
    (unaryFields ns).flatMap booleanBlock = CompletionStripEncoding.unaryFields ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp [UnaryFieldEncoderMachine.unaryFields_cons,UnaryFieldEncoderMachine.unaryField,
      List.flatMap_append,List.flatMap_replicate,booleanBlock,CompletionStripEncoding.unaryFields] at ih ⊢
    exact ih

def prefillEncodingCompiler {input : List Symbol → PeriodicStripTrominoPrefill}
    (height : ScalarCompiler (fun s => (input s).height))
    (period : ScalarCompiler (fun s => (input s).period))
    (motif : PlacementListCompiler (fun s => (input s).motif)) :
    TM2ComputableInPolyTime id CompletionStripEncoding.finEncoding.encode input := by
  let fields := UnaryFieldClosure.appendCompiler id _ _ height
    (UnaryFieldClosure.appendCompiler id _ _ period
      (UnaryFieldClosure.appendCompiler id _ _ motif.count motif.fields))
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime booleanBlock) (fun _ => rfl) (fun _ => rfl)
  let result := TM2CompositionMachine.computableInPolyTime fields raw
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq result
  intro s
  rw [boolean_fields]
  rfl
end LeanTrominoes.CompletionPattern.Runtime
