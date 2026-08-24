/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergePairListScanSemantics

/-! # Exact finite-encoding semantics of guarded word-pair merging -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

@[simp] theorem tokens_encode_componentWords
    (pairs : List (List Bool × List Bool)) :
    tokens (DelimitedBinaryWords.encode (componentWords pairs)) =
      DelimitedBinaryWords.encode (mergedWords pairs) := by
  unfold tokens LightweightFiniteStateTransducer.output componentWords
    mergedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [scan_pairList]
  simp [finish]

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
