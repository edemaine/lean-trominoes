/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnScalarCompiler

/-! # Sparse unary lookup with an exact zero fallback -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

private theorem lookup_absent (candidate : Nat) (keys : List Nat) (q : Nat)
    (datum : Nat → Nat) (absent : q ∉ keys) :
    LastTrueUnaryValueLookupMachine.lookupAux candidate (StableOccurrenceRanks.equalityRow keys q)
      (keys.map datum) = candidate := by
  induction keys generalizing candidate with
  | nil => rfl
  | cons k keys ih =>
    simp only [List.mem_cons,not_or] at absent
    simpa [StableOccurrenceRanks.equalityRow,LastTrueUnaryValueLookupMachine.lookupAux,absent.1] using ih candidate absent.2

theorem lookup_supported (queries keys values : List Nat) (datum : Nat → Nat)
    (correct : values = keys.map datum)
    (support : ∀ q ∈ queries, q ∉ keys → datum q = 0) :
    UnaryKeyedValueLookup.values queries keys values = queries.map datum := by
  rw [UnaryKeyedValueLookup.values_eq_map_lookup,correct]
  apply List.map_congr_left
  intro q hq
  by_cases present : q ∈ keys
  · exact LastTrueUnaryValueLookupMachine.lookup_equalityRow_map datum keys q present
  · rw [LastTrueUnaryValueLookupMachine.lookup,lookup_absent _ _ _ _ present,support q hq present]

variable {Symbol Index Other : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {f : List Symbol → Index → Nat}
  {candidates : List Symbol → List Other} {key value : List Symbol → Other → Nat}

def keyedSupported (queries : Compiler rows f) (keys : Compiler candidates key)
    (values : Compiler candidates value) (datum : List Symbol → Nat → Nat)
    (correct : ∀ s i, i ∈ candidates s → value s i = datum s (key s i))
    (support : ∀ s i, i ∈ rows s → (¬ ∃ j ∈ candidates s, key s j = f s i) → datum s (f s i) = 0) :
    Compiler rows (fun s i => datum s (f s i)) := by
  let result := UnaryKeyedValueLookup.valuesComputableInPolyTime id _ _ _ (fun s => by simp) queries keys values
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [lookup_supported _ _ _ (datum s) (by
    rw [List.map_map]
    exact List.map_congr_left (correct s)) (by
    intro q hq absent
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact support s i hi (by simpa using absent))]
  simp [List.map_map]
end LeanTrominoes.UnaryColumn
