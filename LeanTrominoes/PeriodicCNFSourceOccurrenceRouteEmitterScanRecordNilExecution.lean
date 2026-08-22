/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordMissingExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanRecordData

/-! # Missing-target offset execution inside occurrence scanning -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def scanRecord_nil_evalsInTime (base : TapeData)
    (state : ScanState) (value : Bool)
    (tokens : List SourceOccurrenceRouteTokens.Token)
    (targetsEq : state.targets = []) :
    let next := state.readOffset base.clauseCount.length
      base.literalCount.length value
    EvalsToInTime machine.step
      (beginRecordCfg next.cursor (scanData base state tokens))
      (some (scanOccurrencesCfg next.cursor (scanData base next tokens)))
      (recordTime (scanData base state tokens) 0) := by
  simp only
  have tapeTargetsEq : (scanData base state tokens).targets = [] := by
    simp only [scanData, targetsEq,
      UnaryFieldEncoderMachine.unaryFields_nil]
  have run := recordMissing_evalsInTime
    (state.readOffset base.clauseCount.length
      base.literalCount.length value).cursor
    (scanData base state tokens) rfl tapeTargetsEq
  have finalEq := afterRecord_scanData_eq base state tokens value
  simp only [targetsEq, List.head?_nil, Option.getD_none,
    List.drop_nil, UnaryFieldEncoderMachine.unaryFields_nil] at finalEq
  rw [finalEq] at run
  exact run

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
