/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientation
import LeanTrominoes.PeriodicDrawingFlatEncoding

/-! # Lossless native binary records for colored graph orientation

The encoding stores vertex kinds and colored edge records only. Vertex and
edge counts delimit the tables; signed offsets use the standard integer
encoding. No drawing or compiled constraints are included.
-/
namespace LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding
open Gadget PeriodicCNFFlatEncoding

def colorField : WireColor → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

def decodeColor : Nat → Option WireColor
  | 0 => some .red
  | 1 => some .green
  | 2 => some .blue
  | _ => none

def edgeFields (record : PeriodicEdge Nat × WireColor) : List Nat :=
  [record.1.source,record.1.target,Encodable.encode record.1.offset.1,
    Encodable.encode record.1.offset.2,colorField record.2]

def decodeEdge : List Nat → Option ((PeriodicEdge Nat × WireColor) × List Nat)
  | source::target::x::y::color::rest => do
    let color ← decodeColor color
    return ((⟨source,target,(decodeIntField x,decodeIntField y)⟩,color),rest)
  | _ => none

@[simp] theorem decodeEdge_append (record : PeriodicEdge Nat × WireColor) (rest : List Nat) :
    decodeEdge (edgeFields record ++ rest) = some (record,rest) := by
  rcases record with ⟨⟨source,target,⟨x,y⟩⟩,color⟩
  cases color <;> simp [edgeFields,decodeEdge,colorField,decodeColor]

def decodeEdges : Nat → List Nat → Option (List (PeriodicEdge Nat × WireColor) × List Nat)
  | 0, rest => some ([],rest)
  | n+1, fields => do
    let (edge,rest) ← decodeEdge fields
    let (edges,rest) ← decodeEdges n rest
    return (edge::edges,rest)

@[simp] theorem decodeEdges_append (records : List (PeriodicEdge Nat × WireColor)) (rest : List Nat) :
    decodeEdges records.length (records.flatMap edgeFields ++ rest) = some (records,rest) := by
  induction records with
  | nil => rfl
  | cons record records ih => simp [decodeEdges,List.append_assoc,ih]

def decodeKind : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def fields (input : Input) : List Nat :=
  input.1.length :: input.2.length :: (input.1.map Bool.toNat ++ input.2.flatMap edgeFields)

def decodeFields : List Nat → Option Input
  | vertices::edges::rest => do
    if vertices ≤ rest.length then
      let kinds ← (rest.take vertices).mapM decodeKind
      let (records,tail) ← decodeEdges edges (rest.drop vertices)
      if tail = [] then some (kinds,records) else none
    else none
  | _ => none

private theorem decodeKinds (kinds : List Bool) : (kinds.map Bool.toNat).mapM decodeKind = some kinds := by
  induction kinds with
  | nil => rfl
  | cons kind kinds ih => cases kind <;> simp [decodeKind,ih]

@[simp] theorem decodeFields_fields (input : Input) : decodeFields (fields input) = some input := by
  have edges := decodeEdges_append input.2 []
  simp only [List.append_nil] at edges
  have kinds := decodeKinds input.1
  simp only [List.mapM_map] at kinds
  simp [fields,decodeFields,kinds,edges]

def finEncoding : _root_.LeanTrominoes.FiniteEncoding Input :=
  finEncodingOfFields fields decodeFields decodeFields_fields

@[simp] theorem edgeFields_length (record : PeriodicEdge Nat × WireColor) : (edgeFields record).length = 5 := by
  simp [edgeFields]

theorem fields_length (input : Input) : (fields input).length = 2+input.1.length+5*input.2.length := by
  simp [fields,List.length_flatMap,Nat.mul_comm]
  omega

end LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding
