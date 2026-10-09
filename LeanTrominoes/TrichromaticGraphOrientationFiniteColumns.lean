/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationUnaryEncoding
import LeanTrominoes.EncodedUnaryColumnLookupCompiler
import LeanTrominoes.EncodedUnaryColumnLogicCompiler
import LeanTrominoes.EncodedUnaryColumnCountCompiler
import LeanTrominoes.NP

/-! # Native fields and witness bits for the finite graph verifier -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open _root_.Computability Turing EncodedUnaryColumn
open UnaryFieldEncoderMachine (Symbol unaryFields unaryField)
abbrev WitnessInput := Input × List Bool
def encode := Complexity.encodeWitness UnaryEncoding.finEncoding

def fieldProjection : Sum Symbol (Option Bool) → List Symbol
  | .inl field => [field]
  | .inr _ => []

def bitProjection : Sum Symbol (Option Bool) → List Symbol
  | .inr (some bit) => unaryField bit.toNat
  | _ => []

def fieldsCompiler : TM2ComputableInPolyTime encode unaryFields (fun input : WitnessInput => FlatEncoding.fields input.1) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare encode
    (FiniteBlockTransducer.computableInPolyTime fieldProjection) (fun _ => rfl) (fun _ => rfl)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical
  intro input
  change (((unaryFields (FlatEncoding.fields input.1)).map Sum.inl) ++
    Sum.inr none :: input.2.map (fun bit => Sum.inr (some bit))).flatMap fieldProjection = _
  rw [List.flatMap_append,List.flatMap_cons]
  simp [List.flatMap_map,fieldProjection]

def bitsCompiler : TM2ComputableInPolyTime encode unaryFields (fun input : WitnessInput => input.2.map Bool.toNat) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare encode
    (FiniteBlockTransducer.computableInPolyTime bitProjection) (fun _ => rfl) (fun _ => rfl)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical
  intro input
  change (((unaryFields (FlatEncoding.fields input.1)).map Sum.inl) ++
    Sum.inr none :: input.2.map (fun bit => Sum.inr (some bit))).flatMap bitProjection = _
  rw [List.flatMap_append,List.flatMap_cons]
  simp [List.flatMap_map,bitProjection,unaryFields]

def scalar (value : Nat) : ScalarCompiler encode (fun _ : WitnessInput => value) :=
  TM2ConstantValueCompiler.computableInPolyTime encode unaryFields [value]

def vertexCountCompiler : ScalarCompiler encode (fun input : WitnessInput => input.1.1.length) := by
  let queries : Compiler encode (fun _ : WitnessInput => [()]) (fun _ _ => 0) := scalar 0
  let physical := lookupValues queries fieldsCompiler
  exact TM2ComputableInPolyTime.of_eq physical (fun input => by simp [FlatEncoding.fields])

def edgeCountCompiler : ScalarCompiler encode (fun input : WitnessInput => input.1.2.length) := by
  let queries : Compiler encode (fun _ : WitnessInput => [()]) (fun _ _ => 1) := scalar 1
  let physical := lookupValues queries fieldsCompiler
  exact TM2ComputableInPolyTime.of_eq physical (fun input => by simp [FlatEncoding.fields])

def verticesCompiler : Compiler encode (fun input : WitnessInput => List.range input.1.1.length) (fun _ vertex => vertex) :=
  naturalRange vertexCountCompiler

def edgesCompiler : Compiler encode (fun input : WitnessInput => List.range input.1.2.length) (fun _ edge => edge) :=
  naturalRange edgeCountCompiler

def incidencesCompiler : Compiler encode (fun input : WitnessInput => List.range (2*input.1.2.length)) (fun _ index => index) := by
  let column : Compiler encode (fun _ : WitnessInput => [()]) (fun input _ => input.1.2.length) := edgeCountCompiler
  let count := scale column 2
  exact TM2ComputableInPolyTime.of_eq (naturalRange count) (fun _ => by simp [Nat.mul_comm])

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
end
