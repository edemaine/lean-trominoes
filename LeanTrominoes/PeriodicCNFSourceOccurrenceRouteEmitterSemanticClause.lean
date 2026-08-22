/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticLiteralSuffix

/-! # Semantic execution of one source-occurrence clause block -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

/-- Scanning one canonical clause consumes its aligned targets and emits
exactly the corresponding occurrence-descriptor token blocks. -/
theorem emitAux_clauseTokens (source :
    SourceSplitRouteDescriptorTokens.Source)
    (clause : PeriodicClause Nat) (clauseMem : clause ∈ source.formula.clauses)
    (clauseIndex edgeIndex : Nat)
    (targets : List Nat) (tokens : List SourceOccurrenceRouteTokens.Token)
    (oldClauseIndex : Nat) (oldLiteralIndex : Fin 3)
    (oldAnchorNext : Option Bool) :
    emitAux source.formula.clauses.length
        (PeriodicCNF.presentationLiteralCount source.formula)
        ⟨clauseIndex, oldClauseIndex, edgeIndex, oldLiteralIndex,
          oldAnchorNext,
          entryTargets source.formula
              (clauseEntriesFrom clause clauseIndex 0 edgeIndex clause) ++
            targets⟩
        (SourceOccurrenceRouteTokens.clauseTokens clause ++ tokens) =
      entryTokens source.formula
          (clauseEntriesFrom clause clauseIndex 0 edgeIndex clause) ++
        emitAux source.formula.clauses.length
          (PeriodicCNF.presentationLiteralCount source.formula)
          ⟨clauseIndex + 1, clauseIndex, edgeIndex + clause.length,
            literalIndexAfter oldLiteralIndex 0 clause,
            clauseAnchorState clause, targets⟩ tokens := by
  cases clause with
  | nil =>
      simp [SourceOccurrenceRouteTokens.clauseTokens, clauseEntriesFrom,
        entryTargets_nil, entryTokens_nil, emitAux, literalIndexAfter,
        clauseAnchorState]
  | cons literal literals =>
      have literalMem : literal ∈ literal :: literals := by simp
      have tailMem :
          ∀ tailLiteral ∈ literals, tailLiteral ∈ literal :: literals := by
        intro tailLiteral tailLiteralMem
        simp [tailLiteralMem]
      have width : 1 + literals.length ≤ 3 := by
        have := source.widthAtMostThree
          (literal :: literals) clauseMem
        simp only [PeriodicClause.WidthAtMost, List.length_cons] at this
        omega
      have literalForward := source.isForwardLocal
        (literal :: literals) clauseMem literal literalMem
      have anchorEq :
          PeriodicCNF.clauseAnchor (literal :: literals) =
            (SourceForwardOffset.coordinate
              (SourceForwardOffset.isNext literal), 0) := by
        simp only [PeriodicCNF.clauseAnchor, List.head?_cons,
          Option.map_some, Option.getD_some]
        exact SourceForwardOffset.offset_eq_of_forward literal literalForward
      simp only [SourceOccurrenceRouteTokens.clauseTokens,
        List.zipIdx_cons, List.flatMap_cons, clauseEntriesFrom,
        entryTargets_cons, entryTokens_cons, List.cons_append,
        List.append_assoc, emitAux]
      rw [emitAux_literalTokens source (literal :: literals) clauseMem
        literal literalMem (clauseIndex + 1) clauseIndex edgeIndex 0
        (by omega) (SourceForwardOffset.isNext literal) none (by rfl)
        anchorEq]
      rw [emitAux_literalSuffix source (literal :: literals) clauseMem
        literals tailMem (clauseIndex + 1) clauseIndex 1
        (edgeIndex + 1) width (SourceForwardOffset.isNext literal)
        anchorEq targets tokens (SourceOccurrenceTokens.literalIndex 0)]
      simp only [literalIndexAfter, clauseAnchorState, List.length_cons]
      have edgeEq :
          edgeIndex + 1 + literals.length =
            edgeIndex + (literals.length + 1) := by omega
      rw [edgeEq]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
