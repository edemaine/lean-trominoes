/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BinaryFieldWords
import LeanTrominoes.DelimitedBinaryWordLengthsCompiler
import LeanTrominoes.UnaryFieldAggregateCompiler
import LeanTrominoes.UnaryColumnScalarCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Prepending the field count to native binary input in polynomial time -/
noncomputable section
namespace LeanTrominoes.BinaryFieldCountPreparation
open Turing UnaryColumn PeriodicCNFFlatEncoding
abbrev Symbol := PeriodicCNFFlatEncoding.Symbol

def count (s : List Symbol) : Nat := (BinaryFieldWords.input s).words.length-1

theorem count_encoded (fields : List Nat) : count (encodeNatFields fields) = fields.length := by
  simp [count,BinaryFieldWords.input,BinaryFieldWords.read_fields]

def countCompiler : ScalarCompiler count := by
  let lengths := TM2CompositionMachine.computableInPolyTime BinaryFieldWords.compiler
    DelimitedBinaryWordLengths.valuesComputableInPolyTime
  let counted := TM2CompositionMachine.computableInPolyTime lengths UnaryFieldAggregate.countCompiler
  have column : Compiler (fun _ : List Symbol => [()]) (fun s _ => (BinaryFieldWords.input s).words.length) := by
    apply TM2ComputableInPolyTime.of_eq counted
    intro s
    simp only [DelimitedBinaryWordLengths.values,List.length_map,List.map_cons,List.map_nil]
  apply TM2ComputableInPolyTime.of_eq (sub column (constant column 1))
  intro s
  simp only [count,List.map_cons,List.map_nil]

def preparedSymbols (s : List Symbol) : List Symbol := encodeNatFields [count s] ++ s

def prefixCompiler : TM2ComputableInPolyTime id id preparedSymbols := by
  let binary := TM2CompositionMachine.computableInPolyTime countCompiler UnaryFieldEncoderMachine.computableInPolyTime
  have first : TM2ComputableInPolyTime id id (fun s => encodeNatFields [count s]) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq binary (fun s => (encodeNatFields_eq_trList [count s]).symm)
  have original : TM2ComputableInPolyTime id id (fun s : List Symbol => s) := by
    apply TM2ComputableInPolyTime.of_eq (FiniteBlockTransducer.computableInPolyTime (fun a : Symbol => [a]))
    intro s
    simp
  exact TM2ListAppend.computableInPolyTime first original

theorem prefix_encoded (fields : List Nat) :
    preparedSymbols (encodeNatFields fields) = PartrecToTM2.trList (fields.length::fields) := by
  rw [preparedSymbols,count_encoded,encodeNatFields_eq_trList,encodeNatFields_eq_trList]
  simp [PartrecToTM2.trList]

def compiler {Input : Type} (fields : Input → List Nat) :
    TM2ComputableInPolyTime (fun input => encodeNatFields (fields input)) PartrecToTM2.trList
      (fun input => (fields input).length :: fields input) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare
    (fun input => encodeNatFields (fields input)) prefixCompiler (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical (fun input => prefix_encoded (fields input))

end LeanTrominoes.BinaryFieldCountPreparation
end
