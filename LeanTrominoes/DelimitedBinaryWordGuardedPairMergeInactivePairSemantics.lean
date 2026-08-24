/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeFirstBodySemantics
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeInactiveSecondBodySemantics

/-! # Inactive guarded-pair scan semantics -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_inactivePair
    (first second : List Bool) (suffix : List Token) :
    scan transition .firstStart
        (wordTokens (false :: first) ++ wordTokens second ++ suffix) =
      let rest := scan transition .firstStart suffix
      (rest.1, wordTokens (false :: first) ++ rest.2) := by
  simp only [wordTokens, List.map_cons, List.cons_append,
    scan, transition, List.append_assoc]
  rw [scan_firstBody_bits_wordEnd]
  simp only [List.nil_append]
  simp only [scan, transition]
  rw [scan_inactiveSecondBody_bits_wordEnd]
  simp

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
