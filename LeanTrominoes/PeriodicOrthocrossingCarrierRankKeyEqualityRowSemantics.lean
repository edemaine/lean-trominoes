/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsMatrixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankCompiledKeyEqualitySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowCompiler
import LeanTrominoes.StableOccurrenceRanks

/-! # Semantic rows of compiled carrier-key equality -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEqualityRows

def semanticRows (descriptors : List RouteDescriptor) : List (List Bool) :=
  (CarrierRankCompiledKey.values descriptors).map
    (StableOccurrenceRanks.equalityRow
      (CarrierRankCompiledKey.values descriptors))

@[simp] theorem side_eq_compiledKeys_length
    (descriptors : List RouteDescriptor) :
    side descriptors =
      (CarrierRankCompiledKey.values descriptors).length := by
  simp [side]

/-- Square-row reconstruction turns the unconditional compiled equality
square into the exact equality row of each bundled key. -/
theorem rows_words (descriptors : List RouteDescriptor) :
    (rows descriptors).words = semanticRows descriptors := by
  unfold rows semanticRows StableOccurrenceRanks.equalityRow
  apply BoolSquareRows.delimitedRows_words_of_bits_eq_flatMap
      (squareInput descriptors)
      (CarrierRankCompiledKey.values descriptors)
      (fun first second => decide (first = second))
  · simp
  · exact CarrierRankKeyEquality.bits_eq_compiledKeyEqualityRows descriptors

theorem rows_eq_semanticRows (descriptors : List RouteDescriptor) :
    rows descriptors = ⟨semanticRows descriptors⟩ := by
  have wordEq := rows_words descriptors
  rcases rowEq : rows descriptors with ⟨words⟩
  rw [rowEq] at wordEq
  cases wordEq
  rfl

end CarrierRankKeyEqualityRows
end LeanTrominoes.PeriodicOrthocrossing
