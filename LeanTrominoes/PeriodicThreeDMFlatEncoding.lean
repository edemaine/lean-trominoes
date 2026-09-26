/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.PeriodicDrawingFlatEncoding

/-! # Lossless native binary encodings of periodic 3DM and its supplied drawing

Counts and references are flat natural-number fields. Each reference stores
its element index and two signed offsets, and each triple stores three
references. The planar encoding prefixes a length-delimited complete drawing.
-/
namespace LeanTrominoes.PeriodicThreeDM.FlatEncoding
open PeriodicCNFFlatEncoding

def referenceFields (r : PeriodicThreeDMReference) : List Nat :=
  [r.atom,Encodable.encode r.offset.1,Encodable.encode r.offset.2]

def decodeReference : List Nat → Option (PeriodicThreeDMReference × List Nat)
  | a::x::y::rest => some (⟨a,(decodeIntField x,decodeIntField y)⟩,rest)
  | _ => none

@[simp] theorem decodeReference_append (r : PeriodicThreeDMReference) (rest : List Nat) :
    decodeReference (referenceFields r ++ rest) = some (r,rest) := by
  rcases r with ⟨a,⟨x,y⟩⟩
  simp [referenceFields,decodeReference]

def tripleFields (t : PeriodicThreeDMTriple) : List Nat :=
  referenceFields t.red ++ referenceFields t.green ++ referenceFields t.blue

def decodeTriple (fields : List Nat) : Option (PeriodicThreeDMTriple × List Nat) := do
  let (r,rest) ← decodeReference fields
  let (g,rest) ← decodeReference rest
  let (b,rest) ← decodeReference rest
  return (⟨r,g,b⟩,rest)

@[simp] theorem decodeTriple_append (t : PeriodicThreeDMTriple) (rest : List Nat) :
    decodeTriple (tripleFields t ++ rest) = some (t,rest) := by
  simp [tripleFields,List.append_assoc,decodeTriple]

def decodeTriples : Nat → List Nat → Option (List PeriodicThreeDMTriple × List Nat)
  | 0, rest => some ([],rest)
  | n+1, fields => do
    let (t,rest) ← decodeTriple fields
    let (ts,rest) ← decodeTriples n rest
    return (t::ts,rest)

@[simp] theorem decodeTriples_append (ts : List PeriodicThreeDMTriple) (rest : List Nat) :
    decodeTriples ts.length (ts.flatMap tripleFields ++ rest) = some (ts,rest) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [decodeTriples,List.append_assoc,ih]

def fields (p : PeriodicThreeDM) : List Nat :=
  p.redCount :: p.greenCount :: p.blueCount :: p.triples.length :: p.triples.flatMap tripleFields

def decodeFields : List Nat → Option PeriodicThreeDM
  | r::g::b::n::rest => do
    let (ts,rest) ← decodeTriples n rest
    if rest = [] then some ⟨r,g,b,ts⟩ else none
  | _ => none

@[simp] theorem decodeFields_fields (p : PeriodicThreeDM) : decodeFields (fields p) = some p := by
  have h := decodeTriples_append p.triples []
  simp only [List.append_nil] at h
  simp [fields,decodeFields,h]

def finEncoding : _root_.Computability.FinEncoding PeriodicThreeDM :=
  finEncodingOfFields fields decodeFields decodeFields_fields

@[simp] theorem tripleFields_length (t : PeriodicThreeDMTriple) : (tripleFields t).length = 9 := by
  simp [tripleFields,referenceFields]

theorem fields_length (p : PeriodicThreeDM) : (fields p).length = 4+9*p.triples.length := by
  simp [fields,List.length_flatMap,Nat.mul_comm]
  omega

namespace Planar
open NormalizationCompiler

def fields (i : Input) : List Nat :=
  (PeriodicGridDrawing.Arithmetic.fields i.drawing).length ::
    (PeriodicGridDrawing.Arithmetic.fields i.drawing ++ FlatEncoding.fields i.problem)

def decodeFields : List Nat → Option Input
  | n::rest => do
    let drawing ← PeriodicGridDrawing.Arithmetic.decodeFields (rest.take n)
    let problem ← FlatEncoding.decodeFields (rest.drop n)
    return ⟨problem,drawing⟩
  | [] => none

@[simp] theorem decodeFields_fields (i : Input) : decodeFields (fields i) = some i := by
  simp [fields,decodeFields,PeriodicGridDrawing.Arithmetic.decodeFields_fields]

def finEncoding : _root_.Computability.FinEncoding Input :=
  finEncodingOfFields fields decodeFields decodeFields_fields

end Planar
end LeanTrominoes.PeriodicThreeDM.FlatEncoding
