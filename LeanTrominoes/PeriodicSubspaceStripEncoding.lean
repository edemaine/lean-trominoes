/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripCompletionWindow
import LeanTrominoes.PeriodicCNFFlatEncoding
import LeanTrominoes.PartrecLinearAdaptersSpace

/-! # Native flat cell-record encoding for bounded strip footprints

All names, offsets, counts, and the bounding box are written in binary.
PSPACE membership will restrict the bound by any fixed polynomial in this
native input length.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip
open Computability
abbrev Input := Nat × CompletionData

/-- Reject offsets outside the supplied bounding box. -/
def Problem (input : Input) : Prop := Bounded input.2.1 input.1 ∧ Completable input.2

namespace Encoding

def recordFields (r : (Nat × Nat) × Int) : List Nat := [r.1.1,r.1.2,Encodable.encode r.2]

def decodeRecord : List Nat → Option (((Nat × Nat) × Int) × List Nat)
  | k :: q :: z :: rest => some (((k,q),PeriodicCNFFlatEncoding.decodeIntField z),rest)
  | _ => none

@[simp] theorem decodeRecord_append (r : (Nat × Nat) × Int) (rest : List Nat) :
    decodeRecord (recordFields r ++ rest) = some (r,rest) := by
  rcases r with ⟨⟨k,q⟩,z⟩
  simp [recordFields,decodeRecord]

def decodeRecords : Nat → List Nat → Option (List ((Nat × Nat) × Int) × List Nat)
  | 0,fields => some ([],fields)
  | n+1,fields => do
    let (r,rest) ← decodeRecord fields
    let (rs,tail) ← decodeRecords n rest
    pure (r::rs,tail)

@[simp] theorem decodeRecords_append (rs : List ((Nat × Nat) × Int)) (rest : List Nat) :
    decodeRecords rs.length (rs.flatMap recordFields ++ rest)=some (rs,rest) := by
  induction rs with
  | nil => simp [decodeRecords]
  | cons r rs ih => simp [decodeRecords,ih]

def dataFields (input : Data) : List Nat := input.1 ++ input.2.flatMap recordFields

def fields (input : Input) : List Nat :=
  [input.2.1.2.length,input.1,input.2.1.1.length] ++ dataFields input.2.1 ++
    (input.2.2.length :: input.2.2)

def decode : List Nat → Option Input
  | n :: bound :: count :: rest => do
    let target := rest.take count
    let (rs,tail) ← decodeRecords n (rest.drop count)
    match tail with
    | forcedCount :: forced =>
      if target.length=count ∧ forced.length=forcedCount then some (bound,(target,rs),forced) else none
    | [] => none
  | _ => none

@[simp] theorem decode_fields (input : Input) : decode (fields input) = some input := by
  rcases input with ⟨bound,⟨target,rs⟩,forced⟩
  simp [fields,dataFields,decode,List.append_assoc,List.take_append,List.drop_append]

def finEncoding : _root_.Computability.FinEncoding Input :=
  PeriodicCNFFlatEncoding.finEncodingOfFields fields decode decode_fields

theorem fields_space (input : Input) :
    Turing.PartrecToTM2.encodedListSpace (fields input)=(finEncoding.encode input).length := by
  rw [Turing.PartrecToTM2.encodedListSpace_eq_sum]
  exact (PeriodicCNFFlatEncoding.encodeNatFields_length _).symm

theorem records_le_length (input : Input) : input.2.1.2.length ≤ (finEncoding.encode input).length := by
  have len := Turing.PartrecToTM2.list_length_le_encodedListSpace (fields input)
  rw [fields_space] at len
  have records (rs : List ((Nat × Nat) × Int)) : (rs.flatMap recordFields).length=3*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [recordFields,ih]; omega
  simp only [fields,dataFields,List.length_append,List.length_cons,List.length_nil,records] at len
  omega

end Encoding

/-- A fixed polynomial bound on footprint displacements in the binary input length. -/
def PolynomialBox (p : Polynomial Nat) (input : Input) : Prop :=
  input.1≤p.eval (Encoding.finEncoding.encode input).length
instance (p : Polynomial Nat) (input : Input) : Decidable (PolynomialBox p input) :=
  inferInstanceAs (Decidable (input.1≤p.eval (Encoding.finEncoding.encode input).length))
abbrev PolynomialBoxInput (p : Polynomial Nat) := {input : Input // PolynomialBox p input}

namespace PolynomialBoxEncoding

def fields (p : Polynomial Nat) (input : PolynomialBoxInput p) : List Nat := Encoding.fields input.val

def decode (p : Polynomial Nat) (values : List Nat) : Option (PolynomialBoxInput p) := do
  let input ← Encoding.decode values
  if h : PolynomialBox p input then some ⟨input,h⟩ else none

@[simp] theorem decode_fields (p : Polynomial Nat) (input : PolynomialBoxInput p) :
    decode p (fields p input)=some input := by
  simp only [decode,fields,Encoding.decode_fields,Option.bind_some]
  simp [input.property]

def finEncoding (p : Polynomial Nat) : _root_.Computability.FinEncoding (PolynomialBoxInput p) :=
  PeriodicCNFFlatEncoding.finEncodingOfFields (fields p) (decode p) (decode_fields p)

@[simp] theorem encode_length (p : Polynomial Nat) (input : PolynomialBoxInput p) :
    ((finEncoding p).encode input).length=(Encoding.finEncoding.encode input.val).length := rfl

end PolynomialBoxEncoding
end LeanTrominoes.PeriodicSubspaceTiling.Strip
