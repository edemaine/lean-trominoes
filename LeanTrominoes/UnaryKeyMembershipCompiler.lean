/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryKeyedValueLookupSemantics
import LeanTrominoes.UnaryExactOneBooleanCompiler

/-! # Polynomial-time membership queries in unary key lists -/

noncomputable section
namespace LeanTrominoes.UnaryKeyMembership
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

private theorem lookup_absent (candidate : Nat) (keys : List Nat) (q : Nat) (absent : q ∉ keys) :
    LastTrueUnaryValueLookupMachine.lookupAux candidate (StableOccurrenceRanks.equalityRow keys q)
      (keys.map (fun _ => 1)) = candidate := by
  induction keys generalizing candidate with
  | nil => rfl
  | cons k keys ih =>
    simp only [List.mem_cons,not_or] at absent
    simpa [StableOccurrenceRanks.equalityRow,LastTrueUnaryValueLookupMachine.lookupAux,absent.1] using ih candidate absent.2

theorem values_eq (queries keys : List Nat) :
    UnaryKeyedValueLookup.values queries keys (keys.map (fun _ => 1)) =
      queries.map (fun q => (decide (q ∈ keys)).toNat) := by
  rw [UnaryKeyedValueLookup.values_eq_map_lookup]
  apply List.map_congr_left
  intro q _
  by_cases h : q ∈ keys
  · simpa [h] using LastTrueUnaryValueLookupMachine.lookup_equalityRow_map (fun _ => 1) keys q h
  · simpa [h,LastTrueUnaryValueLookupMachine.lookup] using lookup_absent 0 keys q h

def computableInPolyTime {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (encode : Source → List Symbol) (queries keys : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encode unaryFields queries)
    (keyCompiler : TM2ComputableInPolyTime encode unaryFields keys) :
    TM2ComputableInPolyTime encode id (fun s => (queries s).map (fun q => decide (q ∈ keys s))) := by
  let ones := TM2CompositionMachine.computableInPolyTime keyCompiler UnaryFieldConstantStreams.onesComputableInPolyTime
  let lookup := UnaryKeyedValueLookup.valuesComputableInPolyTime encode queries keys _
    (fun s => by simp [UnaryFieldConstantStreams.ones]) queryCompiler keyCompiler ones
  let bits := TM2CompositionMachine.computableInPolyTime lookup UnaryExactOneBooleans.bitsComputableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq bits
  intro s
  rw [UnaryExactOneBooleans.bits_eq_map]
  change List.map (fun n => decide (n = 1)) (UnaryKeyedValueLookup.values _ _ _) = _
  rw [UnaryFieldConstantStreams.ones,values_eq,List.map_map]
  apply List.map_congr_left
  intro q _
  by_cases h : q ∈ keys s <;> simp [h]

end LeanTrominoes.UnaryKeyMembership
