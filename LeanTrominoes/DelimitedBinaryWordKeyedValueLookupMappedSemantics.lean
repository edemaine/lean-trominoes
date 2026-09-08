/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupSemantics

/-! # Keyed lookup between independently represented query and candidate objects -/

namespace LeanTrominoes.DelimitedBinaryWordKeyedValueLookup

private theorem lookupAux_map_candidates
    {Candidate : Type} (candidates : List Candidate)
    (key : Candidate → List Bool) (datum : Candidate → Nat)
    (target : List Bool) (desired initial : Nat)
    (coherent : ∀ candidate ∈ candidates, target = key candidate → datum candidate = desired) :
    LastTrueUnaryValueLookupMachine.lookupAux initial
        (StableOccurrenceRanks.equalityRow (candidates.map key) target) (candidates.map datum) =
      if target ∈ candidates.map key then desired else initial := by
  induction candidates generalizing initial with
  | nil => simp [StableOccurrenceRanks.equalityRow, LastTrueUnaryValueLookupMachine.lookupAux]
  | cons candidate candidates induction =>
      have tailCoherent : ∀ other ∈ candidates, target = key other → datum other = desired := by
        intro other member equal
        exact coherent other (List.mem_cons_of_mem candidate member) equal
      by_cases same : target = key candidate
      · have valueEq := coherent candidate (by simp) same
        have bitEq : decide (target = key candidate) = true := decide_eq_true same
        simp only [List.map_cons, StableOccurrenceRanks.equalityRow, bitEq,
          LastTrueUnaryValueLookupMachine.lookupAux]
        change LastTrueUnaryValueLookupMachine.lookupAux (datum candidate)
          (StableOccurrenceRanks.equalityRow (candidates.map key) target)
          (candidates.map datum) = _
        rw [induction _ tailCoherent, valueEq]
        simp [same]
      · have bitEq : decide (target = key candidate) = false := decide_eq_false same
        simp only [List.map_cons, StableOccurrenceRanks.equalityRow, bitEq,
          LastTrueUnaryValueLookupMachine.lookupAux]
        change LastTrueUnaryValueLookupMachine.lookupAux initial
          (StableOccurrenceRanks.equalityRow (candidates.map key) target)
          (candidates.map datum) = _
        rw [induction _ tailCoherent]
        simp [same]

/-- Matching keys may connect different object types. If every matching
candidate carries the query's datum and missing queries have datum zero,
lookup recovers the complete query column exactly. -/
theorem values_map_candidates
    {Query Candidate : Type} (queries : List Query) (candidates : List Candidate)
    (queryKey : Query → List Bool) (candidateKey : Candidate → List Bool)
    (queryDatum : Query → Nat) (candidateDatum : Candidate → Nat)
    (coherent : ∀ query ∈ queries, ∀ candidate ∈ candidates,
      queryKey query = candidateKey candidate → candidateDatum candidate = queryDatum query)
    (missingZero : ∀ query ∈ queries,
      queryKey query ∉ candidates.map candidateKey → queryDatum query = 0) :
    values ⟨queries.map queryKey⟩ ⟨candidates.map candidateKey⟩ (candidates.map candidateDatum) =
      queries.map queryDatum := by
  rw [values_eq_map_lookup, List.map_map]
  apply List.map_congr_left
  intro query queryMember
  dsimp only [Function.comp_def]
  unfold LastTrueUnaryValueLookupMachine.lookup
  rw [lookupAux_map_candidates candidates candidateKey candidateDatum (queryKey query)
    (queryDatum query) 0 (coherent query queryMember)]
  by_cases present : queryKey query ∈ candidates.map candidateKey
  · simp [present]
  · simp [present, missingZero query queryMember present]

end LeanTrominoes.DelimitedBinaryWordKeyedValueLookup
