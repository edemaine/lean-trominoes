/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalSuccessorData

/-! # Semantics of global carrier-rank successor bits -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobalSuccessor

private theorem sub_eq_one_iff (first second : Nat) :
    second - first = 1 ↔ second = first + 1 := by
  omega

/-- The compiled excess/exact-one pipeline is the row-major successor
predicate on the global rank column. -/
theorem successorBits_eq_flatMap (descriptors : List RouteDescriptor) :
    successorBits descriptors =
      (CarrierRankGlobal.ranks descriptors).flatMap fun first =>
        (CarrierRankGlobal.ranks descriptors).map fun second =>
          decide (second = first + 1) := by
  unfold successorBits rankExcesses rankWordPairs
  rw [UnaryExactOneBooleans.bits_eq_map]
  unfold DelimitedBinaryWordPairExcessMachine.excesses
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words
  simp only [List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  simp [DelimitedBinaryWordPairExcessMachine.excess,
    UnaryFieldBinaryWords.word, sub_eq_one_iff]

end CarrierRankGlobalSuccessor
end LeanTrominoes.PeriodicOrthocrossing
