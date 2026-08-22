/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.PeriodicCNFSourceForwardOffsetData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInput

/-! # Semantic source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

open SourceOccurrenceRouteTokens

/-- Signed offset fields determined by the two finite forward-local bits. -/
def offsetFields (literalNext anchorNext : Bool) : List Nat :=
  let offset := SourceForwardOffset.relative literalNext anchorNext
  [offset.1.toNat, (-offset.1).toNat,
    offset.2.toNat, (-offset.2).toNat]

/-- The exact eleven fields of one occurrence-prefix route record. -/
def routeFields (clauseCount literalCount clauseIndex edgeIndex : Nat)
    (literalIndex : Fin 3) (targetIndex : Nat)
    (literalNext anchorNext : Bool) : List Nat :=
  [clauseCount + 2 * literalCount,
    3 * literalCount,
    edgeIndex,
    literalCount + clauseIndex,
    targetIndex,
    literalIndex.val,
    0] ++ offsetFields literalNext anchorNext

/-- Counted finite tokens for one occurrence-prefix route record. -/
def routeTokens (clauseCount literalCount clauseIndex edgeIndex : Nat)
    (literalIndex : Fin 3) (targetIndex : Nat)
    (literalNext anchorNext : Bool) :
    List UnaryProgramTokens.Token :=
  CountedUnaryFieldTokens.countedFieldBlock
    (routeFields clauseCount literalCount clauseIndex edgeIndex
      literalIndex targetIndex literalNext anchorNext)

/-- Unbounded semantic cursor mirrored by the finite route-emitter machine's
unary work tapes. -/
structure Cursor where
  nextClauseIndex : Nat
  clauseIndex : Nat
  edgeIndex : Nat
  literalIndex : Fin 3
  anchorNext : Option Bool
  targets : List Nat

def initialCursor (targets : List Nat) : Cursor where
  nextClauseIndex := 0
  clauseIndex := 0
  edgeIndex := 0
  literalIndex := 0
  anchorNext := none
  targets := targets

/-- Consume one target index, defaulting to zero only on malformed words. -/
def Cursor.target (cursor : Cursor) : Nat := cursor.targets.head?.getD 0

def Cursor.remainingTargets (cursor : Cursor) : List Nat :=
  cursor.targets.drop 1

/-- Total semantic parser for arbitrary finite occurrence-route words. -/
def emitAux (clauseCount literalCount : Nat) :
    Cursor → List SourceOccurrenceRouteTokens.Token →
      List UnaryProgramTokens.Token
  | _, [] => []
  | cursor, .clause _ :: tokens =>
      emitAux clauseCount literalCount
        { cursor with
          nextClauseIndex := cursor.nextClauseIndex + 1
          clauseIndex := cursor.nextClauseIndex
          anchorNext := none }
        tokens
  | cursor, .literal index :: tokens =>
      emitAux clauseCount literalCount
        { cursor with literalIndex := index } tokens
  | cursor, .offsetNext literalNext :: tokens =>
      let anchorNext := cursor.anchorNext.getD literalNext
      routeTokens clauseCount literalCount cursor.clauseIndex
          cursor.edgeIndex cursor.literalIndex cursor.target
          literalNext anchorNext ++
        emitAux clauseCount literalCount
          { cursor with
            edgeIndex := cursor.edgeIndex + 1
            anchorNext := some anchorNext
            targets := cursor.remainingTargets }
          tokens
  | cursor, .literalEnd :: tokens =>
      emitAux clauseCount literalCount cursor tokens

/-- Count clauses and literals once, then emit all occurrence-prefix route
records in source presentation order. -/
def emit (input : Input) : List UnaryProgramTokens.Token :=
  emitAux
    (UnaryPolynomialPaddingMachine.selectedCount isClause input.occurrences)
    (UnaryPolynomialPaddingMachine.selectedCount isLiteral input.occurrences)
    (initialCursor input.targets) input.occurrences

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
