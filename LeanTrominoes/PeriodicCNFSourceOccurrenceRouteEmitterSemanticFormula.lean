/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticClause

/-! # Semantic execution of source-occurrence formula tokens -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

theorem entryTargets_append (source : PeriodicCNF Nat)
    (first second : List SemanticEntry) :
    entryTargets source (first ++ second) =
      entryTargets source first ++ entryTargets source second := by
  simp [entryTargets]

theorem entryTokens_append (source : PeriodicCNF Nat)
    (first second : List SemanticEntry) :
    entryTokens source (first ++ second) =
      entryTokens source first ++ entryTokens source second := by
  simp [entryTokens, List.flatMap_append]

/-- Scanning a canonical formula suffix with exactly its aligned target list
emits exactly the corresponding occurrence-descriptor token stream. -/
theorem emitAux_formulaTokens (source :
    SourceSplitRouteDescriptorTokens.Source)
    (clauses : List (PeriodicClause Nat))
    (clausesMem : ∀ clause ∈ clauses, clause ∈ source.formula.clauses)
    (clauseIndex edgeIndex oldClauseIndex : Nat)
    (oldLiteralIndex : Fin 3) (oldAnchorNext : Option Bool) :
    emitAux source.formula.clauses.length
        (PeriodicCNF.presentationLiteralCount source.formula)
        ⟨clauseIndex, oldClauseIndex, edgeIndex, oldLiteralIndex,
          oldAnchorNext,
          entryTargets source.formula
            (formulaEntriesFrom clauses clauseIndex edgeIndex)⟩
        (clauses.flatMap SourceOccurrenceRouteTokens.clauseTokens) =
      entryTokens source.formula
        (formulaEntriesFrom clauses clauseIndex edgeIndex) := by
  induction clauses generalizing clauseIndex edgeIndex oldClauseIndex
      oldLiteralIndex oldAnchorNext with
  | nil =>
      simp [formulaEntriesFrom, entryTargets_nil, entryTokens_nil, emitAux]
  | cons clause clauses induction =>
      have clauseMem : clause ∈ source.formula.clauses :=
        clausesMem clause (by simp)
      have tailMem : ∀ tailClause ∈ clauses,
          tailClause ∈ source.formula.clauses := by
        intro tailClause tailClauseMem
        exact clausesMem tailClause (by simp [tailClauseMem])
      rw [formulaEntriesFrom, entryTargets_append, entryTokens_append,
        List.flatMap_cons, emitAux_clauseTokens source clause clauseMem
          clauseIndex edgeIndex
          (entryTargets source.formula
            (formulaEntriesFrom clauses (clauseIndex + 1)
              (edgeIndex + clause.length)))
          (clauses.flatMap SourceOccurrenceRouteTokens.clauseTokens)
          oldClauseIndex oldLiteralIndex oldAnchorNext]
      rw [induction tailMem (clauseIndex + 1)
        (edgeIndex + clause.length) clauseIndex
        (literalIndexAfter oldLiteralIndex 0 clause)
        (clauseAnchorState clause)]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
