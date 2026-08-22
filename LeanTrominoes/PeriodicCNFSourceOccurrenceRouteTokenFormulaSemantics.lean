/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenClauseSemantics

/-! # Formula semantics of finite source-occurrence route tokens -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

theorem scan_clauseBlocks (clauses : List (PeriodicClause Nat))
    (forward : ∀ clause ∈ clauses, ∀ literal ∈ clause,
      literal.IsForwardLocal) :
    FiniteStateTransducer.scan transition false
        (clauses.flatMap SourceOccurrenceTokens.clauseTokens) =
      (false, clauses.flatMap clauseTokens) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have clauseForward : ∀ literal ∈ clause,
          literal.IsForwardLocal := by
        intro literal literalMem
        exact forward clause (by simp) literal literalMem
      have tailForward : ∀ member ∈ clauses, ∀ literal ∈ member,
          literal.IsForwardLocal := by
        intro member memberMem literal literalMem
        exact forward member (by simp [memberMem]) literal literalMem
      simp only [List.flatMap_cons]
      rw [FiniteStateTransducer.scan_append,
        scan_clauseTokens clause clauseForward]
      simp only
      rw [induction tailForward]

/-- Normalizing the canonical occurrence tokens of a forward-local formula
gives exactly its finite route-information stream. -/
theorem normalize_formulaTokens (formula : PeriodicCNF Nat)
    (forward : formula.IsForwardLocal) :
    normalize (SourceOccurrenceTokens.formulaTokens formula) =
      formulaTokens formula := by
  unfold normalize FiniteStateTransducer.output
    SourceOccurrenceTokens.formulaTokens formulaTokens
  rw [scan_clauseBlocks formula.clauses forward]
  simp [finish]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens
