/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFDeduplication
import Mathlib.Data.Finset.Card

/-! # Exact distinct-variable count through clause deduplication -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Removing duplicate clauses preserves the set, and hence the number, of
distinct variables occurring in a finite periodic-CNF presentation. -/
@[simp]
theorem deduplicate_variableOccurrences_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    source.deduplicate.variableOccurrences.dedup.length =
      source.variableOccurrences.dedup.length := by
  rw [← List.toFinset_card_of_nodup
      (List.nodup_dedup source.deduplicate.variableOccurrences),
    ← List.toFinset_card_of_nodup
      (List.nodup_dedup source.variableOccurrences)]
  congr 1
  ext atom
  simp [PeriodicCNF.variableOccurrences, PeriodicCNF.deduplicate]

end PeriodicCNF
end LeanTrominoes
