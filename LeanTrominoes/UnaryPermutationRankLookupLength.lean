/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryPermutationRankLookupData

/-! # Length of unary permutation-rank lookup output -/

namespace LeanTrominoes
namespace UnaryPermutationRankLookup

/-- Lookup emits one value per deduplicated extended rank, independently of
the aligned field contents. -/
@[simp] theorem values_length (ranks fieldValues : List Nat) :
    (values ranks fieldValues).length = (extendedRanks ranks).dedup.length := by
  simp [values, rankRows, LastTrueUnaryValueLookupMachine.lookups]

end UnaryPermutationRankLookup
end LeanTrominoes
