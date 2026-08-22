/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInitialExecutionData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanToHaltExecution

/-! # Complete execution of source-occurrence route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def totalTime (input : SourceOccurrenceRouteEmitter.Input) : Nat :=
  scanToHaltTime (initialBase input.occurrences)
      (initialScanState input.targets) input.occurrences +
    parseTime input.occurrences
      (UnaryFieldEncoderMachine.unaryFields input.targets)

noncomputable def execution (input : SourceOccurrenceRouteEmitter.Input) :
    EvalsToInTime machine.step
      (scanLeftCfg initialCursor
        ⟨SourceOccurrenceRouteEmitter.encode input,
          [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg initialCursor
        (SourceOccurrenceRouteEmitter.emit input)))
      (totalTime input) := by
  have parseRun := parsing_evalsInTime input.occurrences
    (UnaryFieldEncoderMachine.unaryFields input.targets)
  have parseRun' : EvalsToInTime machine.step
      (scanLeftCfg initialCursor
        ⟨SourceOccurrenceRouteEmitter.encode input,
          [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (scanOccurrencesCfg initialCursor
        ⟨[], [], input.occurrences, [],
          UnaryFieldEncoderMachine.unaryFields input.targets,
          countTape SourceOccurrenceRouteTokens.isClause input.occurrences,
          countTape SourceOccurrenceRouteTokens.isLiteral input.occurrences,
          [], [], [], [], []⟩))
      (parseTime input.occurrences
        (UnaryFieldEncoderMachine.unaryFields input.targets)) := by
    simpa [SourceOccurrenceRouteEmitter.encode,
      SeparatedProductEncoding.encode] using parseRun
  have scanRun := scanToHalt_evalsInTime
    (initialBase input.occurrences) (initialScanState input.targets)
    input.occurrences rfl
  rw [initial_scanData] at scanRun
  dsimp only at scanRun
  rw [initial_scan_emitted input] at scanRun
  have scanRun' : EvalsToInTime machine.step
      (scanOccurrencesCfg initialCursor
        ⟨[], [], input.occurrences, [],
          UnaryFieldEncoderMachine.unaryFields input.targets,
          countTape SourceOccurrenceRouteTokens.isClause input.occurrences,
          countTape SourceOccurrenceRouteTokens.isLiteral input.occurrences,
          [], [], [], [], []⟩)
      (some (haltCfg initialCursor
        (SourceOccurrenceRouteEmitter.emit input)))
      (scanToHaltTime (initialBase input.occurrences)
        (initialScanState input.targets) input.occurrences) := by
    simpa only [initialScanState, initialBase, List.append_nil] using scanRun
  have whole := EvalsToInTime.trans machine.step
    (parseTime input.occurrences
      (UnaryFieldEncoderMachine.unaryFields input.targets))
    (scanToHaltTime (initialBase input.occurrences)
      (initialScanState input.targets) input.occurrences)
    _ _ _ parseRun' scanRun'
  simpa only [totalTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
