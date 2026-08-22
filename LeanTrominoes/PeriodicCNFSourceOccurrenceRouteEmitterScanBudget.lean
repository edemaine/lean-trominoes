/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordTimeBound
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOutputLengthBound
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # A monotone budget for occurrence-stream scanning -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

def scanSize (base : TapeData) (state : ScanState)
    (tokens : List Token) : Nat :=
  base.clauseCount.length + base.literalCount.length +
    state.clauseIndex + state.edgeIndex +
    (UnaryFieldEncoderMachine.unaryFields state.targets).length +
    tokens.length + 1

theorem target_le_unaryFields_length (targets : List Nat) :
    targets.head?.getD 0 ≤
      (UnaryFieldEncoderMachine.unaryFields targets).length := by
  cases targets with
  | nil => simp
  | cons target targets =>
      simp [UnaryFieldEncoderMachine.unaryFields,
        UnaryFieldEncoderMachine.unaryField]

theorem unaryFields_drop_one_length_le (targets : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields (targets.drop 1)).length ≤
      (UnaryFieldEncoderMachine.unaryFields targets).length := by
  cases targets with
  | nil => simp
  | cons target targets =>
      simp [UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryField_length]

theorem scanSize_readClause_le (base : TapeData) (state : ScanState)
    (arity : Fin 4) (tokens : List Token) :
    scanSize base state.readClause tokens ≤
      scanSize base state (.clause arity :: tokens) := by
  cases seenEq : state.cursor.seenClause
  · simp [scanSize, ScanState.readClause, seenEq]
  · simp [scanSize, ScanState.readClause, seenEq]
    omega

theorem scanSize_readLiteral_le (base : TapeData) (state : ScanState)
    (index : Fin 3) (tokens : List Token) :
    scanSize base (state.readLiteral index) tokens ≤
      scanSize base state (.literal index :: tokens) := by
  simp [scanSize, ScanState.readLiteral]

theorem scanSize_readOffset_le (base : TapeData) (state : ScanState)
    (value : Bool) (tokens : List Token) :
    scanSize base
        (state.readOffset base.clauseCount.length
          base.literalCount.length value) tokens ≤
      scanSize base state (.offsetNext value :: tokens) := by
  have targetsLe := unaryFields_drop_one_length_le state.targets
  simp only [scanSize, ScanState.readOffset, List.length_cons]
  omega

theorem scanSize_literalEnd_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    scanSize base state tokens ≤
      scanSize base state (.literalEnd :: tokens) := by
  simp [scanSize]

theorem recordSize_scanData_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    recordSize (scanData base state tokens) (state.targets.head?.getD 0) ≤
      scanSize base state tokens := by
  have targetLe := target_le_unaryFields_length state.targets
  simp only [recordSize, scanData, List.length_replicate, scanSize]
  omega

theorem recordTime_scanData_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    recordTime (scanData base state tokens) (state.targets.head?.getD 0) ≤
      21 * scanSize base state tokens := by
  exact (recordTime_le _ _).trans
    (Nat.mul_le_mul_left 21 (recordSize_scanData_le base state tokens))

theorem routeSize_state_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    SourceOccurrenceRouteEmitter.routeSize base.clauseCount.length
        base.literalCount.length state.clauseIndex state.edgeIndex
        (state.targets.head?.getD 0) ≤
      scanSize base state tokens := by
  have targetLe := target_le_unaryFields_length state.targets
  simp only [SourceOccurrenceRouteEmitter.routeSize, scanSize]
  omega

theorem routeTokens_state_length_le (base : TapeData) (state : ScanState)
    (tokens : List Token) (value : Bool) :
    (SourceOccurrenceRouteEmitter.routeTokens base.clauseCount.length
      base.literalCount.length state.clauseIndex state.edgeIndex
      state.cursor.literalIndex (state.targets.head?.getD 0) value
      (state.cursor.anchorNext.getD value)).length ≤
        15 * scanSize base state tokens := by
  exact (SourceOccurrenceRouteEmitter.routeTokens_length_le _ _ _ _ _ _ _ _).trans
    (Nat.mul_le_mul_left 15 (routeSize_state_le base state tokens))

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
