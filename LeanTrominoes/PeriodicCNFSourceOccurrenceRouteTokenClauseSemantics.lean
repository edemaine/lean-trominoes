/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenSemantics

/-! # Clause semantics of finite source-occurrence route tokens -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

theorem scan_literalBlocks
    (tagged : List (PeriodicLiteral Nat × Nat))
    (forward : ∀ item ∈ tagged, item.1.IsForwardLocal) :
    FiniteStateTransducer.scan transition false
        (tagged.flatMap fun item =>
          SourceOccurrenceTokens.literalTokens item.2 item.1) =
      (false, tagged.flatMap fun item => literalTokens item.2 item.1) := by
  induction tagged with
  | nil => rfl
  | cons item tagged induction =>
      have itemForward : item.1.IsForwardLocal :=
        forward item (by simp)
      have tailForward : ∀ member ∈ tagged,
          member.1.IsForwardLocal := by
        intro member memberMem
        exact forward member (by simp [memberMem])
      simp only [List.flatMap_cons]
      rw [FiniteStateTransducer.scan_append,
        scan_literalTokens item.2 item.1 itemForward]
      simp only
      rw [induction tailForward]

/-- Normalizing one canonical forward-local clause emits its bounded arity
and the finite index/offset block of each literal. -/
theorem scan_clauseTokens (clause : PeriodicClause Nat)
    (forward : ∀ literal ∈ clause, literal.IsForwardLocal) :
    FiniteStateTransducer.scan transition false
        (SourceOccurrenceTokens.clauseTokens clause) =
      (false, clauseTokens clause) := by
  change FiniteStateTransducer.scan transition false
      ([SourceOccurrenceTokens.Token.clause
          (SourceOccurrenceTokens.clauseArity clause.length)] ++
        (clause.zipIdx.flatMap fun tagged =>
          SourceOccurrenceTokens.literalTokens tagged.2 tagged.1)) = _
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan, transition]
  rw [scan_literalBlocks]
  · rfl
  · intro tagged taggedMem
    exact forward tagged.1 (List.fst_mem_of_mem_zipIdx taggedMem)

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens
