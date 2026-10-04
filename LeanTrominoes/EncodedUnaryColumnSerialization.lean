/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.EncodedUnaryColumnCompiler
import LeanTrominoes.UnaryColumnSerialization

/-! # Serializing unary columns from structured source encodings -/
noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)
variable {Input Source Index : Type} [Fintype Source] [Inhabited Source]
  {encodeInput : Input → List Source}
  {rows : Input → List Index} {f : Input → Index → Nat}

def bits (c : Compiler encodeInput rows f) :
    TM2ComputableInPolyTime encodeInput id (fun s => (rows s).map fun i => decide (f s i = 1)) := by
  let result := TM2CompositionMachine.computableInPolyTime c UnaryExactOneBooleans.bitsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => by simp [UnaryExactOneBooleans.bits_eq_map,List.map_map])

def filter {keep : Input → Index → Bool} (c : Compiler encodeInput rows f)
    (control : TM2ComputableInPolyTime encodeInput id (fun s => (rows s).map (keep s))) :
    Compiler encodeInput (fun s => (rows s).filter (keep s)) f := by
  let result := UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime encodeInput _ _ control c
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

abbrev BlocksCompiler (encodeInput : Input → List Source) (rows : Input → List Index) (body : Input → Index → List Symbol) :=
  TM2ComputableInPolyTime encodeInput id (fun s =>
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

def blocks (c : Compiler encodeInput rows f) : BlocksCompiler encodeInput rows (fun s i => unaryField (f s i)) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime unaryBlock) (fun _ => rfl) (fun _ => rfl)
  let result := TM2CompositionMachine.computableInPolyTime c raw
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => by rw [unaryBlock_fields]; simp [List.map_map,Function.comp_def])

def appendBlocks {a b : Input → Index → List Symbol}
    (ca : BlocksCompiler encodeInput rows a) (cb : BlocksCompiler encodeInput rows b) :
    BlocksCompiler encodeInput rows (fun s i => a s i ++ b s i) := by
  let result := FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf encodeInput _ _ ca cb
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  have eq := FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
    ((rows s).map fun i => (a s i,b s i))
  simpa only [id_eq,List.map_map,Function.comp_def] using eq

private def unBlock : FiniteAlphabetDelimitedBlockJoin.Token Symbol → List Symbol
  | .value value => [value]
  | .blockEnd => []

def finishBlocks {body : Input → Index → List Symbol} (c : BlocksCompiler encodeInput rows body) :
    TM2ComputableInPolyTime encodeInput id (fun s => (rows s).flatMap (body s)) := by
  let result := TM2CompositionMachine.computableInPolyTime c (FiniteBlockTransducer.computableInPolyTime unBlock)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  simp [FiniteAlphabetDelimitedBlockJoin.blocks,FiniteAlphabetDelimitedBlockJoin.block,
    List.flatMap_map,List.flatMap_assoc,unBlock]

def triple {g h : Input → Index → Nat}
    (cf : Compiler encodeInput rows f) (cg : Compiler encodeInput rows g) (ch : Compiler encodeInput rows h) :
    TM2ComputableInPolyTime encodeInput unaryFields (fun s => (rows s).flatMap fun i => [f s i,g s i,h s i]) := by
  let result := finishBlocks (appendBlocks (blocks cf) (appendBlocks (blocks cg) (blocks ch)))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  induction rows s with
  | nil => rfl
  | cons i rest ih =>
    simp only [id_eq] at ih
    simp [List.flatMap_cons,
      UnaryFieldEncoderMachine.unaryFields_cons,ih,List.append_assoc]

end LeanTrominoes.EncodedUnaryColumn
