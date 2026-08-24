/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData

/-! # First-body scan semantics for guarded word-pair merging -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

theorem scan_firstBody_bits_wordEnd
    (active : Bool) (bits : List Bool) (suffix : List Token) :
    scan transition (.firstBody active)
        (bits.map Token.bit ++ .wordEnd :: suffix) =
      let rest := scan transition (.secondStart active) suffix
      (rest.1, bits.map Token.bit ++ rest.2) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp [scan, transition, induction]

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
