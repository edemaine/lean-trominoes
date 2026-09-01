/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.UnaryFieldStableDedupSemantics

/-! # Semantics of stable distinct final fan-query keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The distinct compiled key column is stable deduplication of the exact
semantic active-or-fallback fan-query stream. -/
theorem directSourceFinalUniqueFanQueryKeys_eq
    (symbols : List encoding.Γ) :
    directSourceFinalUniqueFanQueryKeys decider symbols =
      (FinalFanQueryRanks.keyedBlocks
        (directSourceFinalAtomIdentityCodes decider symbols)).dedup := by
  unfold directSourceFinalUniqueFanQueryKeys
  rw [UnaryFieldStableDedup.values_eq_dedup,
    directSourceFinalFanQueryKeys_eq_keyedBlocks]

@[simp] theorem directSourceFinalUniqueFanQueryKeys_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalUniqueFanQueryKeys decider symbols).Nodup := by
  unfold directSourceFinalUniqueFanQueryKeys
  rw [UnaryFieldStableDedup.values_eq_dedup]
  exact List.nodup_dedup _

/-- Every stable distinct query remains covered by the unique occurrence
candidate-key column. -/
theorem directSourceFinalUniqueFanQueryKey_mem_candidateKeys
    (symbols : List encoding.Γ) (query : Nat)
    (queryMember :
      query ∈ directSourceFinalUniqueFanQueryKeys decider symbols) :
    query ∈ directSourceFinalOccurrenceCandidateKeys decider symbols := by
  unfold directSourceFinalUniqueFanQueryKeys at queryMember
  rw [UnaryFieldStableDedup.values_eq_dedup, List.mem_dedup] at queryMember
  exact directSourceFinalFanQueryKey_mem_candidateKeys
    decider symbols query queryMember

end LeanTrominoes.PeriodicCNFStripReduction
