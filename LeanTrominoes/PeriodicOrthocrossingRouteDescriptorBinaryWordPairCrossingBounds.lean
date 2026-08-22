/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualityTimeBound
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingBounds

/-! # Output bounds for binary descriptor-pair crossing markers -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWordPairs

/-- One decoded word pair emits at most the fixed descriptor-pair allowance,
and malformed pairs emit nothing. -/
theorem wordPairCrossingMarkers_length_le
    (marker : α) (wordPair : List Bool × List Bool) :
    (wordPairCrossingMarkers marker wordPair).length ≤
      13 * (81 * 81) := by
  unfold wordPairCrossingMarkers
  cases decoded : RouteDescriptorBinaryWords.decodePair wordPair with
  | none => simp
  | some pair =>
      exact routeDescriptorPairCrossingMarkersAtPeriod_length_le
        marker pair.1.gridSize pair

/-- The complete output is linear in the number of input word pairs. -/
theorem crossingMarkers_length_le_pairs
    (marker : α) (input : DelimitedBinaryWordPairs.Input) :
    (crossingMarkers marker input).length ≤
      13 * (81 * 81) * input.pairs.length := by
  rcases input with ⟨pairs⟩
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [crossingMarkers, List.map_cons, List.flatten_cons,
        List.length_append, List.length_cons]
      simp only [crossingMarkers] at induction
      have localBound := wordPairCrossingMarkers_length_le marker pair
      omega

/-- In particular, output length is linear in the complete delimiter encoding
length of the input pair stream. -/
theorem crossingMarkers_length_le_encoding
    (marker : α) (input : DelimitedBinaryWordPairs.Input) :
    (crossingMarkers marker input).length ≤
      13 * (81 * 81) *
        (DelimitedBinaryWordPairs.encode input).length := by
  apply (crossingMarkers_length_le_pairs marker input).trans
  exact Nat.mul_le_mul_left (13 * (81 * 81))
    (DelimitedBinaryWordPairEqualityMachine.pairs_length_le_tokens_length
      input.pairs)

end RouteDescriptorBinaryWordPairs
end PeriodicOrthocrossing
end LeanTrominoes
