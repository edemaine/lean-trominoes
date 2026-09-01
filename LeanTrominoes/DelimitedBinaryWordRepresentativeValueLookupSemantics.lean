/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupCompiler
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSemantics

/-! # Semantics of binary-word representative value lookup -/

namespace LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookup

/-- Mapping a datum over the source words and selecting representative rows
returns that datum once per distinct word, in stable `List.dedup` order. -/
theorem selectedValues_map_eq_dedup_map
    (words : DelimitedBinaryWords.Input)
    (datum : List Bool → Nat) :
    selectedValues words (words.words.map datum) =
      words.words.dedup.map datum := by
  unfold selectedValues DelimitedBinaryWordRepresentativeSquare.rows
  rw [DelimitedBinaryWordEqualitySquare.rows_eq]
  rw [LastRepresentativeEqualityRows.rows_equalityRows]
  unfold LastTrueUnaryValueLookupMachine.lookups
  rw [List.map_map]
  apply List.map_congr_left
  intro word wordMember
  simpa [LastRepresentativeEqualityRows.equalityRow,
    StableOccurrenceRanks.equalityRow] using
    LastTrueUnaryValueLookupMachine.lookup_equalityRow_map
      datum words.words word (List.mem_dedup.mp wordMember)

@[simp] theorem selectedValues_map_length
    (words : DelimitedBinaryWords.Input)
    (datum : List Bool → Nat) :
    (selectedValues words (words.words.map datum)).length =
      words.words.dedup.length := by
  rw [selectedValues_map_eq_dedup_map]
  simp

end LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookup
