/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnScalarCompiler
import LeanTrominoes.UnaryExactOneBooleanCompiler
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler

/-! # Filtering and serializing polynomial-time unary columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)
variable {Source Index : Type} [Fintype Source] [Inhabited Source]
  {rows : List Source → List Index} {f : List Source → Index → Nat}

def bits (c : Compiler rows f) :
    TM2ComputableInPolyTime id id (fun s => (rows s).map fun i => decide (f s i = 1)) := by
  let result := TM2CompositionMachine.computableInPolyTime c UnaryExactOneBooleans.bitsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => by simp [UnaryExactOneBooleans.bits_eq_map,List.map_map])

def filter {keep : List Source → Index → Bool} (c : Compiler rows f)
    (control : TM2ComputableInPolyTime id id (fun s => (rows s).map (keep s))) :
    Compiler (fun s => (rows s).filter (keep s)) f := by
  let result := UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime id _ _ control c
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryFieldBooleanFilter.selectedValues_eq]
  dsimp only
  induction rows s with
  | nil => rfl
  | cons i rest ih =>
    cases h : keep s i <;>
      simp [DelimitedBinaryWordBooleanFilter.selected,h,ih]

abbrev BlocksCompiler (rows : List Source → List Index) (body : List Source → Index → List Symbol) :=
  TM2ComputableInPolyTime id id (fun s =>
    FiniteAlphabetDelimitedBlockJoin.blocks ((rows s).map (body s)))

private def unaryBlock : Symbol → List (FiniteAlphabetDelimitedBlockJoin.Token Symbol)
  | .unit => [.value .unit]
  | .delimiter => [.value .delimiter,.blockEnd]

private theorem unaryBlock_field (n : Nat) :
    (unaryField n).flatMap unaryBlock = FiniteAlphabetDelimitedBlockJoin.block (unaryField n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [unaryField,List.replicate_succ,unaryBlock,FiniteAlphabetDelimitedBlockJoin.block] using
      congrArg (List.cons (FiniteAlphabetDelimitedBlockJoin.Token.value Symbol.unit)) ih

private theorem unaryBlock_fields (ns : List Nat) :
    (unaryFields ns).flatMap unaryBlock = FiniteAlphabetDelimitedBlockJoin.blocks (ns.map unaryField) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [UnaryFieldEncoderMachine.unaryFields_cons,List.flatMap_append,unaryBlock_field,ih]
    rfl

def blocks (c : Compiler rows f) : BlocksCompiler rows (fun s i => unaryField (f s i)) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime unaryBlock) (fun _ => rfl) (fun _ => rfl)
  let result := TM2CompositionMachine.computableInPolyTime c raw
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => by rw [unaryBlock_fields]; simp [List.map_map,Function.comp_def])

def appendBlocks {a b : List Source → Index → List Symbol}
    (ca : BlocksCompiler rows a) (cb : BlocksCompiler rows b) :
    BlocksCompiler rows (fun s i => a s i ++ b s i) := by
  let result := FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf id _ _ ca cb
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  have eq := FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
    ((rows s).map fun i => (a s i,b s i))
  simpa only [id_eq,List.map_map,Function.comp_def] using eq

private def unBlock : FiniteAlphabetDelimitedBlockJoin.Token Symbol → List Symbol
  | .value value => [value]
  | .blockEnd => []

def finishBlocks {body : List Source → Index → List Symbol} (c : BlocksCompiler rows body) :
    TM2ComputableInPolyTime id id (fun s => (rows s).flatMap (body s)) := by
  let result := TM2CompositionMachine.computableInPolyTime c (FiniteBlockTransducer.computableInPolyTime unBlock)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  simp [FiniteAlphabetDelimitedBlockJoin.blocks,FiniteAlphabetDelimitedBlockJoin.block,
    List.flatMap_map,List.flatMap_assoc,unBlock]

def triple {g h : List Source → Index → Nat}
    (cf : Compiler rows f) (cg : Compiler rows g) (ch : Compiler rows h) :
    TM2ComputableInPolyTime id unaryFields (fun s => (rows s).flatMap fun i => [f s i,g s i,h s i]) := by
  let result := finishBlocks (appendBlocks (blocks cf) (appendBlocks (blocks cg) (blocks ch)))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  induction rows s with
  | nil => rfl
  | cons i rest ih =>
    simp only [id_eq] at ih
    simp [List.flatMap_cons,UnaryFieldEncoderMachine.unaryFields_append,
      UnaryFieldEncoderMachine.unaryFields_cons,UnaryFieldEncoderMachine.unaryFields_nil,ih,List.append_assoc]
end LeanTrominoes.UnaryColumn
