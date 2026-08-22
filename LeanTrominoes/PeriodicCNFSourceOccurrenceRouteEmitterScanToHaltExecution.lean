/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInitialScanData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterReverseOutputExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanExecution

/-! # Occurrence scanning through machine halt -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def scanCleanupData (base : TapeData) (state : ScanState)
    (tokens : List SourceOccurrenceRouteTokens.Token) : TapeData :=
  let final := scan base.clauseCount.length base.literalCount.length
    state tokens
  { scanData base final [] with
    outputReverse := []
    output := final.emitted ++ base.output }

def scanToHaltTime (base : TapeData) (state : ScanState)
    (tokens : List SourceOccurrenceRouteTokens.Token) : Nat :=
  let final := scan base.clauseCount.length base.literalCount.length
    state tokens
  cleanupTime (scanCleanupData base state tokens) +
    reverseTime final.emitted.reverse + scanTime base state tokens

noncomputable def scanToHalt_evalsInTime (base : TapeData)
    (state : ScanState) (tokens : List SourceOccurrenceRouteTokens.Token)
    (outputReverseEq : base.outputReverse = []) :
    let final := scan base.clauseCount.length base.literalCount.length
      state tokens
    EvalsToInTime machine.step
      (scanOccurrencesCfg state.cursor (scanData base state tokens))
      (some (haltCfg initialCursor (final.emitted ++ base.output)))
      (scanToHaltTime base state tokens) := by
  simp only
  let final := scan base.clauseCount.length base.literalCount.length
    state tokens
  have throughScan := scan_evalsInTime base state tokens
  have reverseEq : (scanData base final []).outputReverse =
      final.emitted.reverse := by
    simp only [scanData, outputReverseEq, List.append_nil]
  have throughReverse := reverseOutput_evalsInTime final.cursor
    (scanData base final []) final.emitted.reverse reverseEq
  have throughReverse' : EvalsToInTime machine.step
      (reverseOutputCfg final.cursor (scanData base final []))
      (some (cleanupCfg .input final.cursor
        (scanCleanupData base state tokens)))
      (reverseTime final.emitted.reverse) := by
    simpa only [scanCleanupData, final, scanData, List.reverse_reverse]
      using throughReverse
  have cleanupRun := cleanup_evalsInTime final.cursor
    (scanCleanupData base state tokens)
  have cleanupRun' : EvalsToInTime machine.step
      (cleanupCfg .input final.cursor (scanCleanupData base state tokens))
      (some (haltCfg initialCursor (final.emitted ++ base.output)))
      (cleanupTime (scanCleanupData base state tokens)) := by
    simpa only [scanCleanupData, final, scanData] using cleanupRun
  have throughCleanup := EvalsToInTime.trans machine.step
    (reverseTime final.emitted.reverse)
    (cleanupTime (scanCleanupData base state tokens))
    (reverseOutputCfg final.cursor (scanData base final []))
    (cleanupCfg .input final.cursor (scanCleanupData base state tokens))
    (some (haltCfg initialCursor (final.emitted ++ base.output)))
    throughReverse' cleanupRun'
  have whole := EvalsToInTime.trans machine.step
    (scanTime base state tokens)
    (cleanupTime (scanCleanupData base state tokens) +
      reverseTime final.emitted.reverse)
    (scanOccurrencesCfg state.cursor (scanData base state tokens))
    (reverseOutputCfg final.cursor (scanData base final []))
    (some (haltCfg initialCursor (final.emitted ++ base.output)))
    throughScan throughCleanup
  simpa only [scanToHaltTime, final] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
