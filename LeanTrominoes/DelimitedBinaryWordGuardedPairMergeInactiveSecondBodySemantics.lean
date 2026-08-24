/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData

/-! # Inactive second-body scan semantics for guarded word-pair merging -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_inactiveSecondBody_bits_wordEnd
    (bits : List Bool) (suffix : List Token) :
    scan transition (.secondBody false)
        (bits.map Token.bit ++ .wordEnd :: suffix) =
      let rest := scan transition .firstStart suffix
      (rest.1, .wordEnd :: rest.2) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp [scan, transition, induction]

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
