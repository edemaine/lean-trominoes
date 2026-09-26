/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.PeriodicThreeDMGraph
import LeanTrominoes.UnaryColumnSerialization
import LeanTrominoes.UnaryFieldClosure

/-! # Native 3DM fields assembled from colored incidence columns -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.FlatEncoding
open Turing UnaryColumn

def incidenceReference (p : PeriodicThreeDM) (tag : IncidenceTag) : PeriodicThreeDMReference :=
  (p.triples.getD tag.tripleIndex default).reference tag.color

theorem incidenceFields_eq (p : PeriodicThreeDM) :
    p.incidenceTags.flatMap (fun tag => referenceFields (incidenceReference p tag)) =
      p.triples.flatMap tripleFields := by
  unfold incidenceTags
  rw [List.flatMap_assoc]
  have rows : p.triples.zipIdx.flatMap (fun tagged => tripleFields tagged.1) = p.triples.flatMap tripleFields := by
    simpa only [List.flatMap_map] using congrArg (List.flatMap tripleFields) (List.zipIdx_map_fst 0 p.triples)
  rw [← rows]
  apply List.flatMap_congr
  intro tagged ht
  have bounds := List.mem_zipIdx' ht
  have atIndex : p.triples.getD tagged.2 default = tagged.1 := by
    rw [List.getD_eq_getElem _ _ bounds.1]
    exact bounds.2.symm
  simp only [tripleIncidenceTags,incidenceColors,incidenceReference,List.flatMap_cons,List.flatMap_nil,
    List.flatMap_map,atIndex,tripleFields,PeriodicThreeDMTriple.reference,List.append_assoc,List.append_nil]

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol] {problem : List Symbol → PeriodicThreeDM}

def bodyCompiler
    (atoms : Compiler (fun s => (problem s).incidenceTags) (fun s t => (incidenceReference (problem s) t).atom))
    (x : Compiler (fun s => (problem s).incidenceTags) (fun s t => Encodable.encode (incidenceReference (problem s) t).offset.1))
    (y : Compiler (fun s => (problem s).incidenceTags) (fun s t => Encodable.encode (incidenceReference (problem s) t).offset.2)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (problem s).triples.flatMap tripleFields) := by
  apply TM2ComputableInPolyTime.of_eq (triple atoms x y)
  intro s
  exact incidenceFields_eq (problem s)

def fieldsCompiler
    (red : ScalarCompiler (fun s => (problem s).redCount))
    (green : ScalarCompiler (fun s => (problem s).greenCount))
    (blue : ScalarCompiler (fun s => (problem s).blueCount))
    (count : ScalarCompiler (fun s => (problem s).triples.length))
    (body : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (problem s).triples.flatMap tripleFields)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s => fields (problem s)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _ red
    (UnaryFieldClosure.appendCompiler id _ _ green
      (UnaryFieldClosure.appendCompiler id _ _ blue
        (UnaryFieldClosure.appendCompiler id _ _ count body)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rfl

def encodingCompiler
    (compiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s => fields (problem s))) :
    TM2ComputableInPolyTime id finEncoding.encode problem := by
  let physical := TM2CompositionMachine.computableInPolyTime compiler UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList (fields (problem s))).symm

end LeanTrominoes.PeriodicThreeDM.FlatEncoding
end
