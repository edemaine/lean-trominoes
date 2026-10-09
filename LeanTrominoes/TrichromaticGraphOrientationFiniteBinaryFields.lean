/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteBinaryNormalization
import LeanTrominoes.TrichromaticGraphOrientationFiniteColumns
import LeanTrominoes.DelimitedBinaryWordLengthsCompiler

/-! # Expanding only polynomially bounded binary graph fields -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
open _root_.Computability Turing EncodedUnaryColumn
open UnaryFieldEncoderMachine (unaryFields)
abbrev WitnessInput := FiniteVerifier.WitnessInput
def encode := Complexity.encodeWitness FlatEncoding.finEncoding

def projection : Sum PeriodicCNFFlatEncoding.Symbol (Option Bool) → List PeriodicCNFFlatEncoding.Symbol
  | .inl symbol => [symbol]
  | .inr _ => []

def binaryFieldsCompiler : TM2ComputableInPolyTime encode id
    (fun s : WitnessInput => FlatEncoding.finEncoding.encode s.1) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare encode
    (FiniteBlockTransducer.computableInPolyTime projection) (fun _ => rfl) (fun _ => rfl)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical
  intro s
  change (((PeriodicCNFFlatEncoding.encodeNatFields (FlatEncoding.fields s.1)).map Sum.inl) ++
    Sum.inr none::s.2.map (fun bit => Sum.inr (some bit))).flatMap projection = _
  have erase : s.2.flatMap (fun _ => ([] : List PeriodicCNFFlatEncoding.Symbol))=[] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  simp [List.flatMap_map,projection,erase,FlatEncoding.finEncoding,PeriodicCNFFlatEncoding.finEncodingOfFields]

def rawBound (symbols : List PeriodicCNFFlatEncoding.Symbol) : Nat := (BinaryFieldWords.readWords symbols).length+3

def rawBoundCompiler : UnaryColumn.ScalarCompiler rawBound := by
  let lengths := TM2CompositionMachine.computableInPolyTime BinaryFieldWords.compiler
    DelimitedBinaryWordLengths.valuesComputableInPolyTime
  let counted := TM2CompositionMachine.computableInPolyTime lengths UnaryFieldAggregate.countCompiler
  let column : Compiler id (fun _ : List PeriodicCNFFlatEncoding.Symbol => [()])
      (fun symbols _ => (BinaryFieldWords.readWords symbols).length) :=
    counted.of_eq (fun _ => by simp [DelimitedBinaryWordLengths.values,BinaryFieldWords.input])
  exact add column (constant column 3)

def decodedFields (s : WitnessInput) : List Nat :=
  (FlatEncoding.fields s.1 ++ [0]).map (BinaryFieldBoundedDecoder.cap (bound s.1))

def decodedFieldsCompiler : TM2ComputableInPolyTime encode unaryFields decodedFields := by
  let physical := TM2CompositionMachine.computableInPolyTime binaryFieldsCompiler
    (BinaryFieldBoundedDecoder.compiler rawBoundCompiler)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have count : rawBound (FlatEncoding.finEncoding.encode s.1)=bound s.1 := by
    simp [rawBound,FlatEncoding.finEncoding,PeriodicCNFFlatEncoding.finEncodingOfFields,
      BinaryFieldWords.read_fields,bound]
  rw [count]
  exact BinaryFieldBoundedDecoder.values_fields _ (by have := (bound_counts s.1).2.2; omega) _

theorem decodedFields_sub_one (s : WitnessInput) :
    (decodedFields s).map (fun value => value-1)=FlatEncoding.fields (normalize s.1) ++ [0] := by
  have positive : 0<bound s.1 := by have := (bound_counts s.1).2.2; omega
  simp only [decodedFields,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    ← capped_eq_decoder,← fields_normalize]
  simp [capped,positive]

def normalizedFieldsCompiler : TM2ComputableInPolyTime encode unaryFields
    (fun s : WitnessInput => FlatEncoding.fields (normalize s.1)) := by
  let values : Compiler encode decodedFields (fun _ value => value) :=
    decodedFieldsCompiler.of_eq (fun _ => by simp)
  let total := countRows values
  let totalColumn : Compiler encode (fun _ : WitnessInput => [()]) (fun s _ => (decodedFields s).length) := total
  let count := sub totalColumn (constant totalColumn 1)
  let indices := naturalRange count
  let physical := lookupValues indices (sub values (constant values 1))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  change (List.range ((decodedFields s).length-1)).map
    (fun index => ((decodedFields s).map (fun value => value-1)).getD index 0) = _
  rw [decodedFields_sub_one]
  have length : (decodedFields s).length-1=(FlatEncoding.fields (normalize s.1)).length := by
    have h := congrArg List.length (decodedFields_sub_one s)
    simp only [List.length_map,List.length_append,List.length_cons,List.length_nil] at h
    omega
  rw [length]
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_map,List.getElem_range]
    rw [List.getD_append _ _ _ _ (by simpa using rightBound),List.getD_eq_getElem _ _ rightBound]

end LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
end
