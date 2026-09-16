/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryNaturalRangeCompiler
import LeanTrominoes.UnaryKeyedValueLookupSemantics

/-! # Scalar bounds and keyed lookups for unary columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {f : List Symbol → Index → Nat}
  {n : List Symbol → Nat}

abbrev ScalarCompiler (n : List Symbol → Nat) :=
  TM2ComputableInPolyTime id unaryFields (fun s => [n s])

def naturalRange (c : ScalarCompiler n) : Compiler (fun s => List.range (n s)) (fun _ i => i) := by
  let scalar : TM2ComputableInPolyTime id (fun n => unaryFields [n]) n :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq c (fun _ => rfl)
  let result := TM2CompositionMachine.computableInPolyTime scalar UnaryNaturalRange.computableInPolyTime
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp)

def broadcast (c : Compiler rows f) (scalar : ScalarCompiler n) : Compiler rows (fun s _ => n s) := by
  let result := UnaryIndexedValueLookup.valuesComputableInPolyTime id _ _ (constant c 0) scalar
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by simp)]
  simp [List.map_map]

def multiplyScalar (c : Compiler rows f) (scalar : ScalarCompiler n) :
    Compiler rows (fun s i => f s i*n s) := by
  let result := UnaryFieldScalarMultiply.computableInPolyTime id n _ scalar c
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp [List.map_map])

def keyed {Other : Type} {candidates : List Symbol → List Other}
    {key value : List Symbol → Other → Nat} (queries : Compiler rows f)
    (keys : Compiler candidates key) (values : Compiler candidates value)
    (datum : List Symbol → Nat → Nat)
    (correct : ∀ s i, i ∈ candidates s → value s i = datum s (key s i))
    (present : ∀ s i, i ∈ rows s → ∃ j ∈ candidates s, key s j = f s i) :
    Compiler rows (fun s i => datum s (f s i)) := by
  let result := UnaryKeyedValueLookup.valuesComputableInPolyTime id _ _ _ (fun s => by simp) queries keys values
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryKeyedValueLookup.values_eq_map_datum _ _ _ (datum s) (by
    rw [List.map_map]
    exact List.map_congr_left (correct s)) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    obtain ⟨j,hj,eq⟩ := present s i hi
    exact List.mem_map.mpr ⟨j,hj,eq⟩)]
  simp [List.map_map]
end LeanTrominoes.UnaryColumn
