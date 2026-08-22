/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanRecordData

/-! # Present-target offset execution inside occurrence scanning -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def scanRecord_cons_evalsInTime (base : TapeData)
    (state : ScanState) (value : Bool)
    (tokens : List SourceOccurrenceRouteTokens.Token)
    (target : Nat) (remaining : List Nat)
    (targetsEq : state.targets = target :: remaining) :
    let next := state.readOffset base.clauseCount.length
      base.literalCount.length value
    EvalsToInTime machine.step
      (beginRecordCfg next.cursor (scanData base state tokens))
      (some (scanOccurrencesCfg next.cursor (scanData base next tokens)))
      (recordTime (scanData base state tokens) target) := by
  simp only
  have tapeTargetsEq : (scanData base state tokens).targets =
      List.replicate target .unit ++ .delimiter ::
        UnaryFieldEncoderMachine.unaryFields remaining := by
    simp only [scanData, targetsEq,
      UnaryFieldEncoderMachine.unaryFields_cons,
      UnaryFieldEncoderMachine.unaryField, List.append_assoc,
      List.singleton_append]
  have run := record_evalsInTime
    (state.readOffset base.clauseCount.length
      base.literalCount.length value).cursor
    (scanData base state tokens) target
    (UnaryFieldEncoderMachine.unaryFields remaining) rfl tapeTargetsEq
  have finalEq := afterRecord_scanData_eq base state tokens value
  simp [targetsEq] at finalEq
  rw [finalEq] at run
  exact run

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
