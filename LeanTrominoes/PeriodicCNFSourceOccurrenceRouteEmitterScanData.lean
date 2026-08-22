/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordTokenSemantics

/-! # Occurrence-scan state for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

/-- Pure state changed while the machine scans normalized occurrences. -/
structure ScanState where
  cursor : Cursor
  clauseIndex : Nat
  edgeIndex : Nat
  targets : List Nat
  emitted : List OutputToken

def ScanState.semanticCursor (state : ScanState) :
    SourceOccurrenceRouteEmitter.Cursor where
  nextClauseIndex :=
    if state.cursor.seenClause then state.clauseIndex + 1
    else state.clauseIndex
  clauseIndex := state.clauseIndex
  edgeIndex := state.edgeIndex
  literalIndex := state.cursor.literalIndex
  anchorNext := state.cursor.anchorNext
  targets := state.targets

def ScanState.readClause (state : ScanState) : ScanState :=
  { state with
    cursor :=
      { state.cursor with seenClause := true, anchorNext := none }
    clauseIndex :=
      if state.cursor.seenClause then state.clauseIndex + 1
      else state.clauseIndex }

def ScanState.readLiteral (state : ScanState) (index : Fin 3) : ScanState :=
  { state with cursor := { state.cursor with literalIndex := index } }

def ScanState.readOffset (clauseCount literalCount : Nat)
    (state : ScanState) (value : Bool) : ScanState :=
  let anchorNext := state.cursor.anchorNext.getD value
  let target := state.targets.head?.getD 0
  { state with
    cursor :=
      { state.cursor with
        anchorNext := some anchorNext
        currentNext := value }
    edgeIndex := state.edgeIndex + 1
    targets := state.targets.drop 1
    emitted := state.emitted ++
      SourceOccurrenceRouteEmitter.routeTokens clauseCount literalCount
        state.clauseIndex state.edgeIndex state.cursor.literalIndex
        target value anchorNext }

def scan (clauseCount literalCount : Nat) :
    ScanState → List Token → ScanState
  | state, [] => state
  | state, .clause _ :: tokens =>
      scan clauseCount literalCount state.readClause tokens
  | state, .literal index :: tokens =>
      scan clauseCount literalCount (state.readLiteral index) tokens
  | state, .offsetNext value :: tokens =>
      scan clauseCount literalCount
        (state.readOffset clauseCount literalCount value) tokens
  | state, .literalEnd :: tokens =>
      scan clauseCount literalCount state tokens

/-- Realize a pure scan state on the changing machine tapes. -/
def scanData (base : TapeData) (state : ScanState)
    (occurrences : List Token) : TapeData :=
  { base with
    occurrences := occurrences
    targets := UnaryFieldEncoderMachine.unaryFields state.targets
    clauseIndex := List.replicate state.clauseIndex ()
    edgeIndex := List.replicate state.edgeIndex ()
    scratch := []
    outputReverse := state.emitted.reverse ++ base.outputReverse }

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
