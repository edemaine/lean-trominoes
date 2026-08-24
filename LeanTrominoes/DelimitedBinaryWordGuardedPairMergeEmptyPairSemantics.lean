/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeInactiveSecondBodySemantics

/-! # Empty-first-word pair scan semantics -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_emptyPair (second : List Bool) (suffix : List Token) :
    scan transition .firstStart
        (wordTokens [] ++ wordTokens second ++ suffix) =
      let rest := scan transition .firstStart suffix
      (rest.1, wordTokens [] ++ rest.2) := by
  simp only [wordTokens, List.map_nil, List.nil_append,
    List.append_assoc, List.cons_append]
  simp only [scan, transition]
  rw [scan_inactiveSecondBody_bits_wordEnd]
  rfl

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
