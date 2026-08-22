/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # Offset-record scan-state normalization -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem afterRecord_scanData_eq (base : TapeData) (state : ScanState)
    (tokens : List SourceOccurrenceRouteTokens.Token) (value : Bool) :
    let next := state.readOffset base.clauseCount.length
      base.literalCount.length value
    afterFinishedRecordData
        (afterRecordCounters (beginRecordData (scanData base state tokens)))
        (state.targets.head?.getD 0)
        (UnaryFieldEncoderMachine.unaryFields (state.targets.drop 1))
        next.cursor.literalIndex next.cursor.currentNext
        next.cursor.anchorValue =
      scanData base next tokens := by
  simp only
  rw [afterFinishedRecordData_eq_routeTokens]
  simp only [scanData, ScanState.readOffset, List.length_replicate,
    Cursor.anchorValue, Option.getD_some, List.replicate_succ,
    List.reverse_append, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
