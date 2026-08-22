/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticLiteralStep

/-! # Semantic execution of a source-occurrence literal suffix -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

@[simp] theorem entryTargets_nil (source : PeriodicCNF Nat) :
    entryTargets source [] = [] := rfl

@[simp] theorem entryTargets_cons (source : PeriodicCNF Nat)
    (entry : SemanticEntry) (entries : List SemanticEntry) :
    entryTargets source (entry :: entries) =
      (PeriodicThreeSATThree.occurrenceRouteDescriptor
        source entry.1 entry.2).targetVertexIndex ::
        entryTargets source entries := rfl

@[simp] theorem entryTokens_nil (source : PeriodicCNF Nat) :
    entryTokens source [] = [] := rfl

@[simp] theorem entryTokens_cons (source : PeriodicCNF Nat)
    (entry : SemanticEntry) (entries : List SemanticEntry) :
    entryTokens source (entry :: entries) =
      CountedUnaryFieldTokens.countedFieldBlock
          (PeriodicThreeSATThree.occurrenceRouteDescriptor
            source entry.1 entry.2).unaryFields ++
        entryTokens source entries := rfl

/-- Scanning a width-three literal suffix consumes exactly its aligned target
indices and emits exactly its occurrence-descriptor token blocks. -/
theorem emitAux_literalSuffix (source :
    SourceSplitRouteDescriptorTokens.Source)
    (clause : PeriodicClause Nat) (clauseMem : clause ∈ source.formula.clauses)
    (literals : List (PeriodicLiteral Nat))
    (literalsMem : ∀ literal ∈ literals, literal ∈ clause)
    (nextClauseIndex clauseIndex literalIndex edgeIndex : Nat)
    (width : literalIndex + literals.length ≤ 3)
    (anchorNext : Bool)
    (anchorEq : PeriodicCNF.clauseAnchor clause =
      (SourceForwardOffset.coordinate anchorNext, 0))
    (targets : List Nat) (tokens : List SourceOccurrenceRouteTokens.Token)
    (oldLiteralIndex : Fin 3) :
    emitAux source.formula.clauses.length
        (PeriodicCNF.presentationLiteralCount source.formula)
        ⟨nextClauseIndex, clauseIndex, edgeIndex, oldLiteralIndex,
          some anchorNext,
          entryTargets source.formula
              (clauseEntriesFrom clause clauseIndex literalIndex edgeIndex
                literals) ++ targets⟩
        (((literals.zipIdx literalIndex).flatMap (fun taggedLiteral =>
            SourceOccurrenceRouteTokens.literalTokens
              taggedLiteral.2 taggedLiteral.1)) ++ tokens) =
      entryTokens source.formula
          (clauseEntriesFrom clause clauseIndex literalIndex edgeIndex
            literals) ++
        emitAux source.formula.clauses.length
          (PeriodicCNF.presentationLiteralCount source.formula)
          ⟨nextClauseIndex, clauseIndex, edgeIndex + literals.length,
            literalIndexAfter oldLiteralIndex literalIndex literals,
            some anchorNext, targets⟩ tokens := by
  induction literals generalizing literalIndex edgeIndex oldLiteralIndex with
  | nil =>
      simp [clauseEntriesFrom, entryTargets_nil, entryTokens_nil,
        literalIndexAfter]
  | cons literal literals induction =>
      simp only [List.length_cons] at width
      have literalMem : literal ∈ clause :=
        literalsMem literal (by simp)
      have tailMem : ∀ tailLiteral ∈ literals, tailLiteral ∈ clause := by
        intro tailLiteral tailLiteralMem
        exact literalsMem tailLiteral (by simp [tailLiteralMem])
      have literalIndexLt : literalIndex < 3 := by omega
      have tailWidth : literalIndex + 1 + literals.length ≤ 3 := by
        omega
      simp only [List.zipIdx_cons, List.flatMap_cons, clauseEntriesFrom,
        entryTargets_cons, entryTokens_cons, List.cons_append,
        List.append_assoc]
      rw [emitAux_literalTokens source clause clauseMem literal literalMem
        nextClauseIndex clauseIndex edgeIndex literalIndex literalIndexLt
        anchorNext (some anchorNext) (by simp) anchorEq]
      rw [induction tailMem (literalIndex + 1) (edgeIndex + 1)
        tailWidth (SourceOccurrenceTokens.literalIndex literalIndex)]
      simp only [literalIndexAfter, List.length_cons]
      have edgeEq :
          edgeIndex + 1 + literals.length =
            edgeIndex + (literals.length + 1) := by omega
      rw [edgeEq]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
