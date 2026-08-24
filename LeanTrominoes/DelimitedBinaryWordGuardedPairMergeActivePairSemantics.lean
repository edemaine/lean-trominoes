/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeActiveSecondBodySemantics
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeFirstBodySemantics

/-! # Active guarded-pair scan semantics -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_activePair
    (first second : List Bool) (suffix : List Token) :
    scan transition .firstStart
        (wordTokens (true :: first) ++ wordTokens second ++ suffix) =
      let rest := scan transition .firstStart suffix
      (rest.1,
        wordTokens ((true :: first) ++ second) ++ rest.2) := by
  simp only [wordTokens, List.map_cons, List.cons_append,
    scan, transition, List.append_assoc]
  rw [scan_firstBody_bits_wordEnd]
  simp only [List.nil_append]
  simp only [scan, transition]
  rw [scan_activeSecondBody_bits_wordEnd]
  simp [List.map_append, List.append_assoc]

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
