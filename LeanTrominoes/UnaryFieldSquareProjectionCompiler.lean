/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldPairPresenceCompiler

/-! # Unary coordinate projections of ordered field products -/

noncomputable section
namespace LeanTrominoes.UnaryFieldSquareProjection
open Computability Turing
open UnaryFieldEncoderMachine (unaryField unaryFields)
abbrev Side := UnaryFieldPairPresence.Side
abbrev Token := DelimitedBinaryWordPairs.Token
abbrev Symbol := UnaryFieldEncoderMachine.Symbol

def choose {α : Type} (side : Side) (a b : α) : α :=
  match side with | .first => a | .second => b

def block (side : Side) : Token → List Symbol
  | .firstBit _ => choose side [.unit] []
  | .secondBit _ => choose side [] [.unit]
  | .pairEnd => [.delimiter]
  | _ => []

theorem block_pair (side : Side) (a b : List Bool) :
    (DelimitedBinaryWordPairs.pairTokens (a,b)).flatMap (block side) =
      unaryField (choose side a.length b.length) := by
  have first (word : List Bool) :
      (word.map DelimitedBinaryWordPairs.Token.firstBit).flatMap (block side) =
        choose side (List.replicate word.length UnaryFieldEncoderMachine.Symbol.unit) [] := by
    induction word with
    | nil => cases side <;> rfl
    | cons bit word ih => cases side <;> simp_all [block,choose,List.replicate_succ]
  have second (word : List Bool) :
      (word.map DelimitedBinaryWordPairs.Token.secondBit).flatMap (block side) =
        choose side [] (List.replicate word.length UnaryFieldEncoderMachine.Symbol.unit) := by
    induction word with
    | nil => cases side <;> rfl
    | cons bit word ih => cases side <;> simp_all [block,choose,List.replicate_succ]
  simp only [DelimitedBinaryWordPairs.pairTokens,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,block,List.nil_append,List.append_nil]
  rw [first,second]
  cases side <;> simp [choose,unaryField]

def lengths (side : Side) (input : DelimitedBinaryWordPairs.Input) : List Nat :=
  input.pairs.map fun pair => choose side pair.1.length pair.2.length

theorem block_fields (side : Side) (input : DelimitedBinaryWordPairs.Input) :
    (DelimitedBinaryWordPairs.encode input).flatMap (block side) = unaryFields (lengths side input) := by
  unfold DelimitedBinaryWordPairs.encode lengths unaryFields
  rw [List.flatMap_assoc,List.flatMap_map]
  apply List.flatMap_congr
  rintro ⟨a,b⟩ _
  exact block_pair side a b

def lengthsCompiler (side : Side) : TM2ComputableInPolyTime
    DelimitedBinaryWordPairs.finEncoding.encode unaryFields (lengths side) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare DelimitedBinaryWordPairs.finEncoding.encode
    (FiniteBlockTransducer.computableInPolyTime (block side)) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq raw (block_fields side)

def values (side : Side) (source : List Nat) : List Nat :=
  source.flatMap fun a => source.map fun b => choose side a b

def computableInPolyTime (side : Side) : TM2ComputableInPolyTime unaryFields unaryFields (values side) := by
  let pairs := TM2CompositionMachine.computableInPolyTime UnaryFieldBinaryWords.wordsComputableInPolyTime
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let projected := TM2CompositionMachine.computableInPolyTime pairs (lengthsCompiler side)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq projected
  intro source
  congr 1
  simp [lengths,DelimitedBinaryWordPairProductMachine.pairs,UnaryFieldBinaryWords.words,
    UnaryFieldBinaryWords.word,values,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

end LeanTrominoes.UnaryFieldSquareProjection
