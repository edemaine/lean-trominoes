/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticEntries
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenSemantics

/-! # Semantic execution of one source-occurrence literal block -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

/-- One canonical literal block consumes its aligned target and emits exactly
the counted unary record of the corresponding occurrence descriptor. -/
theorem emitAux_literalTokens (source :
    SourceSplitRouteDescriptorTokens.Source)
    (clause : PeriodicClause Nat) (clauseMem : clause ∈ source.formula.clauses)
    (literal : PeriodicLiteral Nat) (literalMem : literal ∈ clause)
    (nextClauseIndex clauseIndex edgeIndex literalIndex : Nat)
    (literalIndexLt : literalIndex < 3) (anchorNext : Bool)
    (anchorState : Option Bool)
    (anchorStateEq :
      anchorState.getD (SourceForwardOffset.isNext literal) = anchorNext)
    (anchorEq : PeriodicCNF.clauseAnchor clause =
      (SourceForwardOffset.coordinate anchorNext, 0))
    (targets : List Nat) (tokens : List SourceOccurrenceRouteTokens.Token)
    (oldLiteralIndex : Fin 3) :
    emitAux source.formula.clauses.length
        (PeriodicCNF.presentationLiteralCount source.formula)
        ⟨nextClauseIndex, clauseIndex, edgeIndex, oldLiteralIndex,
          anchorState,
          (PeriodicThreeSATThree.occurrenceRouteDescriptor source.formula
            ⟨clauseIndex, clause, literalIndex, literal⟩ edgeIndex).targetVertexIndex ::
            targets⟩
        (SourceOccurrenceRouteTokens.literalTokens literalIndex literal ++
          tokens) =
      CountedUnaryFieldTokens.countedFieldBlock
          (PeriodicThreeSATThree.occurrenceRouteDescriptor source.formula
            ⟨clauseIndex, clause, literalIndex, literal⟩ edgeIndex).unaryFields ++
        emitAux source.formula.clauses.length
          (PeriodicCNF.presentationLiteralCount source.formula)
          ⟨nextClauseIndex, clauseIndex, edgeIndex + 1,
            SourceOccurrenceTokens.literalIndex literalIndex,
            some anchorNext, targets⟩ tokens := by
  have literalIndexEq :
      (SourceOccurrenceTokens.literalIndex literalIndex).val = literalIndex := by
    simp [SourceOccurrenceTokens.literalIndex, Fin.ofNat,
      Nat.mod_eq_of_lt literalIndexLt]
  have recordEq :=
    routeTokens_eq_occurrenceRouteDescriptor_countedFieldBlock
      source.formula
      (CNFIncidence.mk clauseIndex clause literalIndex literal)
      edgeIndex (SourceOccurrenceTokens.literalIndex literalIndex)
      anchorNext
      (source.isForwardLocal clause clauseMem literal literalMem)
      literalIndexEq anchorEq
  simp only [SourceOccurrenceRouteTokens.literalTokens, emitAux,
    Cursor.target, Cursor.remainingTargets, List.head?_cons,
    List.cons_append, List.nil_append]
  rw [anchorStateEq]
  exact congrArg
    (fun emitted => emitted ++
      emitAux source.formula.clauses.length
        (PeriodicCNF.presentationLiteralCount source.formula)
        ⟨nextClauseIndex, clauseIndex, edgeIndex + 1,
          SourceOccurrenceTokens.literalIndex literalIndex,
          some anchorNext, targets⟩ tokens)
    recordEq

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
