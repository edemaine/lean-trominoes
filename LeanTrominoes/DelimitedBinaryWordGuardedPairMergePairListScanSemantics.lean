/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergePairSemantics

/-! # Scan semantics of explicit guarded word-pair lists -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_pairList (pairs : List (List Bool × List Bool)) :
    scan transition .firstStart
        (pairs.flatMap fun pair =>
          wordTokens pair.1 ++ wordTokens pair.2) =
      (.firstStart,
        (pairs.map fun pair => mergePair pair.1 pair.2).flatMap
          wordTokens) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [scan_pair, induction]

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
