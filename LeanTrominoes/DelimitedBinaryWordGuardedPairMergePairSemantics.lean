/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeActivePairSemantics
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeEmptyPairSemantics
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeInactivePairSemantics

/-! # One-pair scan semantics for guarded word merging -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_pair (first second : List Bool) (suffix : List Token) :
    scan transition .firstStart
        (wordTokens first ++ wordTokens second ++ suffix) =
      let rest := scan transition .firstStart suffix
      (rest.1, wordTokens (mergePair first second) ++ rest.2) := by
  cases first with
  | nil => exact scan_emptyPair second suffix
  | cons guard first =>
      cases guard with
      | false => exact scan_inactivePair first second suffix
      | true => exact scan_activePair first second suffix

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
