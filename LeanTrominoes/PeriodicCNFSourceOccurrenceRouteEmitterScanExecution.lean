/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanBoundarySteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanClauseStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanLiteralOffsetSteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanRecordExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanTime

/-! # Complete occurrence-scan execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

noncomputable def scan_evalsInTime (base : TapeData)
    (state : ScanState) (tokens : List Token) :
    EvalsToInTime machine.step
      (scanOccurrencesCfg state.cursor (scanData base state tokens))
      (some (reverseOutputCfg
        (scan base.clauseCount.length base.literalCount.length
          state tokens).cursor
        (scanData base
          (scan base.clauseCount.length base.literalCount.length
            state tokens) [])))
      (scanTime base state tokens) := by
  induction tokens generalizing state with
  | nil =>
      have step := oneStep (step_scanData_nil base state)
      simpa only [scan, scanTime] using step
  | cons token tokens induction =>
      cases token with
      | clause arity =>
          have first := oneStep (step_scanData_clause base state arity tokens)
          have rest := induction state.readClause
          have whole := EvalsToInTime.trans machine.step 1
            (scanTime base state.readClause tokens)
            (scanOccurrencesCfg state.cursor
              (scanData base state (.clause arity :: tokens)))
            (scanOccurrencesCfg state.readClause.cursor
              (scanData base state.readClause tokens))
            (some (reverseOutputCfg
              (scan base.clauseCount.length base.literalCount.length
                state.readClause tokens).cursor
              (scanData base
                (scan base.clauseCount.length base.literalCount.length
                  state.readClause tokens) [])))
            first rest
          simpa only [scan, scanTime] using whole
      | literal index =>
          have first := oneStep
            (step_scanData_literal base state index tokens)
          have rest := induction (state.readLiteral index)
          have whole := EvalsToInTime.trans machine.step 1
            (scanTime base (state.readLiteral index) tokens)
            (scanOccurrencesCfg state.cursor
              (scanData base state (.literal index :: tokens)))
            (scanOccurrencesCfg (state.readLiteral index).cursor
              (scanData base (state.readLiteral index) tokens))
            (some (reverseOutputCfg
              (scan base.clauseCount.length base.literalCount.length
                (state.readLiteral index) tokens).cursor
              (scanData base
                (scan base.clauseCount.length base.literalCount.length
                  (state.readLiteral index) tokens) [])))
            first rest
          simpa only [scan, scanTime] using whole
      | offsetNext value =>
          let next := state.readOffset base.clauseCount.length
            base.literalCount.length value
          have first := oneStep
            (step_scanData_offset base state value tokens)
          have recordRun := scanRecord_evalsInTime base state value tokens
          have throughRecord := EvalsToInTime.trans machine.step 1
            (recordTime (scanData base state tokens)
              (state.targets.head?.getD 0))
            (scanOccurrencesCfg state.cursor
              (scanData base state (.offsetNext value :: tokens)))
            (beginRecordCfg next.cursor (scanData base state tokens))
            (some (scanOccurrencesCfg next.cursor
              (scanData base next tokens))) first recordRun
          have rest := induction next
          have whole := EvalsToInTime.trans machine.step
            (recordTime (scanData base state tokens)
                (state.targets.head?.getD 0) + 1)
            (scanTime base next tokens)
            (scanOccurrencesCfg state.cursor
              (scanData base state (.offsetNext value :: tokens)))
            (scanOccurrencesCfg next.cursor (scanData base next tokens))
            (some (reverseOutputCfg
              (scan base.clauseCount.length base.literalCount.length
                next tokens).cursor
              (scanData base
                (scan base.clauseCount.length base.literalCount.length
                  next tokens) [])))
            throughRecord rest
          simpa only [scan, scanTime, next] using whole
      | literalEnd =>
          have first := oneStep
            (step_scanData_literalEnd base state tokens)
          have rest := induction state
          have whole := EvalsToInTime.trans machine.step 1
            (scanTime base state tokens)
            (scanOccurrencesCfg state.cursor
              (scanData base state (.literalEnd :: tokens)))
            (scanOccurrencesCfg state.cursor (scanData base state tokens))
            (some (reverseOutputCfg
              (scan base.clauseCount.length base.literalCount.length
                state tokens).cursor
              (scanData base
                (scan base.clauseCount.length base.literalCount.length
                  state tokens) [])))
            first rest
          simpa only [scan, scanTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
