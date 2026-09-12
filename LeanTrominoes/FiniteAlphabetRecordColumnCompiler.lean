/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Shared unary-field serialization and aligned record-column joining -/

noncomputable section
namespace LeanTrominoes.FiniteAlphabetRecordColumns
open Computability Turing
variable {Alphabet : Type} [Fintype Alphabet]
abbrev PackedToken (Alphabet : Type) := FiniteAlphabetDelimitedBlockJoin.Token Alphabet

private def unaryBlock (unitToken : Alphabet) (suffix : List Alphabet) :
    UnaryFieldEncoderMachine.Symbol → List (PackedToken Alphabet)
  | .unit => [.value unitToken]
  | .delimiter => suffix.map .value ++ [.blockEnd]

omit [Fintype Alphabet] in
private theorem unaryBlock_field (unitToken : Alphabet) (suffix : List Alphabet) (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap (unaryBlock unitToken suffix) =
      FiniteAlphabetDelimitedBlockJoin.block (List.replicate value unitToken ++ suffix) := by
  induction value with
  | zero => simp [UnaryFieldEncoderMachine.unaryField, unaryBlock, FiniteAlphabetDelimitedBlockJoin.block]
  | succ value induction =>
      simpa only [UnaryFieldEncoderMachine.unaryField, List.replicate_succ,
        List.cons_append, List.flatMap_cons, unaryBlock, List.singleton_append, List.nil_append,
        FiniteAlphabetDelimitedBlockJoin.block, List.map_cons] using
        congrArg (List.cons (.value unitToken)) induction

omit [Fintype Alphabet] in
private theorem unaryBlock_fields (unitToken : Alphabet) (suffix : List Alphabet) (values : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields values).flatMap (unaryBlock unitToken suffix) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (values.map (fun value => List.replicate value unitToken ++ suffix)) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        unaryBlock_field, induction]
      rfl

/-- Convert each unary field to one end-delimited finite-alphabet record column. -/
noncomputable def unaryBlocksComputableInPolyTime (unitToken : Alphabet) (suffix : List Alphabet) :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id
      (fun values => FiniteAlphabetDelimitedBlockJoin.blocks
        (values.map (fun value => List.replicate value unitToken ++ suffix))) :=
  TM2PolyTimeInputEncodingTransport.of_prepare UnaryFieldEncoderMachine.unaryFields
    (FiniteBlockTransducer.computableInPolyTime (unaryBlock unitToken suffix))
    (fun _ => rfl) (unaryBlock_fields unitToken suffix)

/-- Join two independently compiled columns without changing the common row order. -/
noncomputable def joinedFieldsComputableInPolyTime
    {Source SourceSymbol Row : Type} [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol) (rows : Source → List Row)
    (first second : Source → Row → List Alphabet)
    (firstCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks ((rows source).map (first source))))
    (secondCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks ((rows source).map (second source)))) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks
        ((rows source).map (fun row => first source row ++ second source row))) := by
  let joined := FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf
    encodeSource _ _ firstCompiler secondCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq joined (fun source => by
    simpa only [List.map_map, Function.comp_def, id_eq] using
      FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
        ((rows source).map (fun row => (first source row, second source row))))

private def unpackBlock : PackedToken Alphabet → List Alphabet
  | .value token => [token]
  | .blockEnd => []

omit [Fintype Alphabet] in
private theorem unpack_blocks (bodies : List (List Alphabet)) :
    (FiniteAlphabetDelimitedBlockJoin.blocks bodies).flatMap unpackBlock = bodies.flatten := by
  simp only [FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_assoc,
    FiniteAlphabetDelimitedBlockJoin.block, List.flatMap_append, List.flatMap_map,
    unpackBlock, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp

/-- Remove the temporary joining delimiters after all record fields are assembled. -/
noncomputable def flattenBlocksComputableInPolyTime
    {Source SourceSymbol : Type} [Fintype SourceSymbol] [Inhabited Alphabet]
    (encodeSource : Source → List SourceSymbol) (bodies : Source → List (List Alphabet))
    (compiler : TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks (bodies source))) :
    TM2ComputableInPolyTime encodeSource id (fun source => (bodies source).flatten) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (TM2CompositionMachine.computableInPolyTime compiler
      (FiniteBlockTransducer.computableInPolyTime unpackBlock))
    (fun source => unpack_blocks (bodies source))

end LeanTrominoes.FiniteAlphabetRecordColumns
end
