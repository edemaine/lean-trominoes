/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordLastIndexIdentitySemantics

/-! # Data retrieved through a represented key's last occurrence index -/

namespace LeanTrominoes.LastTrueUnaryValueLookupMachine

/-- The last matching key index is in range whenever its source value occurs. -/
theorem lookup_mappedKey_range_lt {Value Key : Type} [DecidableEq Key]
    (values : List Value) (key : Value → Key) (target : Value) (member : target ∈ values) :
    lookup (StableOccurrenceRanks.equalityRow (values.map key) (key target))
      (List.range (values.map key).length) < values.length := by
  obtain ⟨index, bound, selected, _keyEq⟩ := lookup_equalityRow_range_selected
    (values.map key) (key target) (List.mem_map.mpr ⟨target, member, rfl⟩)
  rw [selected]
  simpa only [List.length_map] using bound

/-- A last-index identity retrieves any datum coherent on equal represented
keys, even when the source list contains repeated occurrences. -/
theorem getD_lookup_mappedKey_range {Value Key : Type} [DecidableEq Key]
    (values : List Value) (key : Value → Key) (datum : Value → Nat)
    (target : Value) (member : target ∈ values)
    (coherent : ∀ value ∈ values, key value = key target → datum value = datum target) :
    (values.map datum).getD
      (lookup (StableOccurrenceRanks.equalityRow (values.map key) (key target))
        (List.range (values.map key).length)) 0 = datum target := by
  obtain ⟨index, bound, selected, keyEq⟩ := lookup_equalityRow_range_selected
    (values.map key) (key target) (List.mem_map.mpr ⟨target, member, rfl⟩)
  have valueBound : index < values.length := by simpa only [List.length_map] using bound
  have datumBound : index < (values.map datum).length := by simpa only [List.length_map] using valueBound
  rw [selected, List.getD_eq_getElem _ _ datumBound, List.getElem_map]
  apply coherent (values[index]'valueBound) (List.getElem_mem valueBound)
  simpa only [List.getElem_map] using keyEq

end LeanTrominoes.LastTrueUnaryValueLookupMachine
