/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanQueryRankKeyCoverage

/-! # Mapping semantic final-fan query-key blocks -/

namespace LeanTrominoes.FinalFanQueryRanks

/-- Mapping over all semantic fan-query keys distributes into the explicit
three-rank block of every presented identity. -/
theorem map_keyedBlocks {Output : Type*} (function : Nat → Output)
    (values : List Nat) :
    (keyedBlocks values).map function =
      values.flatMap fun value =>
        (block (BoundedPositiveCountPreds.boundedPositiveCountPred
          (values.count value))).map fun rank =>
            function (value * 3 + rank.val) := by
  unfold keyedBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro value valueMember
  simp [List.map_map, Function.comp_def]

end LeanTrominoes.FinalFanQueryRanks
